#!/usr/bin/env python3
"""Bind the completed independent selection audit to actual publication Git blobs.

This reviewer uses stdlib and read-only Git calls. It does not invoke publication,
installation, solution-extraction, browser, or compiler helpers.
"""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT / "reports/book/publication-repo"
REPORT = ROOT / "reports/solution-review/source91-content-selection-independent-review-v1.json"
PLAN = "reports/solution-review/source91-content-publication-plan-v1.json"
INPUTS = "reports/solution-review/source91-content-publication-files-v1.json"
PREFLIGHT = "reports/solution-review/source91-content-selection-preflight-v1.json"
RELEASE = "book/solutions/releases/source91-v1/plan.json"
READY = "reports/solution-review/source91-release-ready-v1.json"
INSTALLED = "reports/solution-review/source91-installed-independent-review-v1.json"
EXPECTED_COMMIT = "e98d46758478cf51f5be2e6f66381596756ab572"


def reference(path):
    raw = (ROOT / path).read_bytes()
    return {"file": path, "sha256": hashlib.sha256(raw).hexdigest()}


def read(path):
    return json.loads((ROOT / path).read_bytes())


def git(*args):
    return subprocess.run(["git", "-C", str(REPO), *args], check=True,
                          capture_output=True).stdout


def main():
    if REPORT.exists():
        raise RuntimeError("Refusing to overwrite an immutable review")
    plan, inputs, preflight, release = map(read, (PLAN, INPUTS, PREFLIGHT, RELEASE))
    errors = []
    refs = {p: reference(p) for p in (PLAN, INPUTS, PREFLIGHT, RELEASE, READY, INSTALLED)}
    expected_refs = {
        PLAN: "021514aa9c7ae41d49bd9f5bf16c21904d8d048577b7d8c609ab667f6d2dfa30",
        INPUTS: "3a4adf13e515b62a39dc459dd881a8d6452e0c0d7d35716f649977a73da55b94",
        PREFLIGHT: "227165b601f0eb8fde1aa92f175b3502065191501ac6232f41ea430955714fc1",
        RELEASE: "58455c17c48c091f9c6934165d64d003ff43bfee7bda888d10f438d02e7cc11e",
        READY: "a367e36d28ad76509caaaf8ab3fcdf075e1dcbcd6560ca68872d301cc424243d",
        INSTALLED: "621e46f3da6d8290c6a06b061bb8e14805edcfaae04aeb27135c4deba93567e4",
    }
    for path, expected in expected_refs.items():
        if refs[path]["sha256"] != expected:
            errors.append({"type": "evidence_hash_mismatch", "file": path})
    rows = plan["files"]
    paths = [row["file"] for row in rows]
    if len(paths) != 2289 or len(set(paths)) != len(paths) or paths != inputs:
        errors.append({"type": "plan_list_mismatch"})
    if preflight["status"] != "passed_preflight":
        errors.append({"type": "preflight_not_passed"})
    for field in ("missing_required_evidence", "forbidden_or_symlink_paths",
                  "current_source_hash_mismatches", "publication_destination_hash_mismatches",
                  "missing_or_wrong_site31", "missing_or_wrong_source44"):
        if preflight[field]:
            errors.append({"type": "preflight_findings", "field": field})
    if preflight["publication_plan"] != refs[PLAN] or preflight["input_list"] != refs[INPUTS]:
        errors.append({"type": "preflight_binding_mismatch"})
    checked = {row["file"]: row for row in preflight["checked_files"]}
    if set(checked) != set(paths) or any(checked[p]["sha256"] != row["sha256"]
                                       for p, row in zip(paths, rows)):
        errors.append({"type": "preflight_file_binding_mismatch"})
    head = git("rev-parse", "HEAD").decode().strip()
    parents = git("show", "--format=%P", "--no-patch", head).decode().split()
    clean = not git("status", "--porcelain")
    if head != EXPECTED_COMMIT or parents != [plan["expected_publication_head"]] or not clean:
        errors.append({"type": "publication_commit_state_mismatch",
                       "head": head, "parents": parents, "clean": clean})
    expected = {row["file"]: row["sha256"] for row in rows}
    expected[PLAN] = refs[PLAN]["sha256"]
    proc = subprocess.Popen(["git", "-C", str(REPO), "cat-file", "--batch"],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    commit_files = []
    for path, sha in expected.items():
        if "\n" in path or "\r" in path:
            raise RuntimeError("Unsafe path in immutable selection")
        proc.stdin.write((head + ":" + path + "\n").encode())
        proc.stdin.flush()
        header = proc.stdout.readline().decode().rstrip("\n")
        parts = header.split()
        if len(parts) != 3 or parts[1] != "blob":
            errors.append({"type": "missing_or_nonblob_commit_file", "file": path, "header": header})
            continue
        size = remaining = int(parts[2])
        digest = hashlib.sha256()
        while remaining:
            chunk = proc.stdout.read(min(1048576, remaining))
            if not chunk:
                raise RuntimeError("Unexpected Git blob EOF")
            digest.update(chunk)
            remaining -= len(chunk)
        if proc.stdout.read(1) != b"\n":
            raise RuntimeError("Malformed Git batch framing")
        actual = digest.hexdigest()
        commit_files.append({"file": path, "git_blob": parts[0], "sha256": actual, "bytes": size})
        if actual != sha:
            errors.append({"type": "commit_blob_hash_mismatch", "file": path,
                           "expected_sha256": sha, "actual_sha256": actual})
    proc.stdin.close()
    stderr = proc.stderr.read().decode()
    if proc.wait() != 0 or stderr:
        errors.append({"type": "git_batch_failure", "stderr": stderr})
    changed = set(git("diff-tree", "--no-commit-id", "--name-only", "-r", "-z", head)
                  .decode().rstrip("\0").split("\0"))
    expected_changed = {row["file"] for row in rows if row["sha256"] != row["before_sha256"]} | {PLAN}
    if changed != expected_changed:
        errors.append({"type": "commit_delta_mismatch", "unexpected": sorted(changed - expected_changed),
                       "missing": sorted(expected_changed - changed)})
    report = {
        "schema": "source91-content-selection-independent-review-v1",
        "status": "approved" if not errors else "needs_revision",
        "errors": errors,
        "reviewer": "/root/review_gaussian35",
        "method": "Independent stdlib native SHA256/path-selection audit; this supplemental reviewer streams actual Git blobs with read-only cat-file --batch and checks the exact commit delta. No Root install/stage/check helper was invoked.",
        "helper": reference(str(Path(__file__).relative_to(ROOT))),
        "publication_plan": refs[PLAN], "input_list": refs[INPUTS],
        "independent_preflight": refs[PREFLIGHT], "release_plan": refs[RELEASE],
        "release_ready": refs[READY], "installed_independent_review": refs[INSTALLED],
        "counts": {"selected_content_files": len(rows), "selected_content_bytes": preflight["total_bytes"],
                   "approved_site_assets": 31, "source_targets": 44, "selected_pages": 22,
                   "selected_exercises": 556, "replace": 251, "retain": 305,
                   "selected_drafts": len(release["drafts"]),
                   "selected_independent_math_depth_reviews": len(release["independent_reviews"]),
                   "explicit_required_evidence_files": preflight["required_evidence_file_count"],
                   "actual_commit_files_verified": len(commit_files), "actual_commit_changed_files": len(changed),
                   "compiled_or_unselected_Lean_payloads": preflight["compiled_or_unselected_Lean_file_count"],
                   "runtime_and_cache_payloads": preflight["runtime_and_cache_payload_count"]},
        "selected_drafts": release["drafts"],
        "selected_independent_math_depth_reviews": release["independent_reviews"],
        "required_evidence_files": preflight["required_evidence_files"],
        "selection_exclusions": "No .git/.lake/cache/runtime/archive/source-object directories, symlinks, compiled code files, or unselected Lean sources appear in the selected payload. Receipt/helper names containing runtime are evidence, not runtime copies.",
        "pdf_classification": preflight["pdf_classification"],
        "publication_commit": {"head": head, "parents": parents, "clean_worktree_at_review": clean,
                               "exact_delta_matches_plan": changed == expected_changed,
                               "verified_files": commit_files},
        "scope": "Selection and committed-byte review only. The 22 existing selected independent reviews provide completed math/student-depth judgments; no new math, browser, or compiler success is inferred here. Formal correspondence for rewritten Source91 answers remains pending explicit rebase; historical Source90/checkpoint35 coverage is separate.",
        "preserved_attempts": "Preflight records its initial additional clean-checkout assumption failing during authorized staging; no approval was emitted at that attempt. Both immutable installation parser/check failure receipts are in the required preserved evidence.",
        "whitespace_disposition": reference("reports/solution-review/source91-whitespace-check-disposition-v1.json"),
        "later_metadata": "This review, its independent preflight and helper, and later whitespace/metadata-review receipts were created after the frozen content plan. Root will include them in the subsequent metadata selection; they are not added retroactively to this content plan.",
        "push_or_live_delivery_claimed": False,
    }
    REPORT.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"report": reference(str(REPORT.relative_to(ROOT))), "status": report["status"],
                      "errors": errors, "counts": report["counts"]}))
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
