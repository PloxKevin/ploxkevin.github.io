#!/usr/bin/env python3
"""Record three actual, independent Source90 browser commands without site/proof edits."""
from pathlib import Path
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ref(path):
    return {'file': str(path.relative_to(ROOT)), 'sha256': sha(path), 'bytes': path.stat().st_size}


def main():
    summary_path = OUT / 'browser34-source90-actual-execution-summary-v1.json'
    assert not summary_path.exists()
    application_review = OUT / 'independent-actual-source89-90-application-review-v1.json'
    assert json.loads(application_review.read_bytes())['errors'] == []
    assert sha(ROOT / 'book/coverage/inventory-after-correction90.json') == 'fa3edbc297c59878db2226a04dc91e66493f5bf9adb67535c05b60429e1ac254'
    expected_pages = {'SafeLearning/nn-in-the-loop.html': '22b785e46001e4e5d73166d05503f9beb5454634cfa6b929df24f6bbe33e7e4b',
                      'SafeLearning/primer-probability.html': '19891bd487ec19b67cbda477809a3a273242c6d4b0647e93c01b94f75108519f'}
    assert all(sha(ROOT / name) == fingerprint for name, fingerprint in expected_pages.items())
    selection_path = ROOT / 'reports/full-coverage/checkpoint-33-selection.json'
    selection = json.loads(selection_path.read_bytes())
    protected = {name: row['sha256'] for name, row in selection['proof_files'].items()}
    for name, fingerprint in protected.items():
        assert sha(ROOT / name) == fingerprint
    site = [p for p in (ROOT / 'SafeLearning').iterdir() if p.is_file() and p.suffix in ('.html', '.css', '.js')]
    assert len(site) == 31
    future = [ROOT / 'verification/lean/SafeLearning' / name for name in [
        'CompleteModulesNNScalarOriginLinearization34.lean', 'CompleteModulesShiftedTemporalIQC34.lean',
        'CompleteAppliedConditionalExpectationMSEDensityWhole34.lean']]
    for path in [*site, *future, ROOT / 'book/coverage/inventory.json', ROOT / 'book/coverage/inventory-after-correction90.json',
                 ROOT / 'book/coverage/material-corrections.json', selection_path, ROOT / 'qa/learning_review.mjs',
                 ROOT / 'qa/book_browser_checks.mjs', OUT / 'source90_changed_regions_and_scalar_finite34_v1.mjs',
                 application_review, Path(__file__)]:
        protected[str(path.relative_to(ROOT))] = sha(path)

    def guard():
        return [name for name, fingerprint in protected.items() if sha(ROOT / name) != fingerprint]

    baseline_path = OUT / 'browser34-source90-site31-selected33-plus-three34-protected-baseline-v1.json'
    assert not baseline_path.exists() and guard() == []
    baseline_path.write_text(json.dumps({'protected_sha256': protected, 'selected33_proofs': len(selection['proof_files']),
        'new34_canonical_proofs': 3, 'site_assets': 31,
        'concurrent_authorized_Root_owner_aggregate_progress_and_publication_work_excluded_from_browser_stability_guard': True}, indent=2) + '\n')
    commands = []
    for kind, page in [('NN-full-page', 'nn-in-the-loop.html'), ('probability-full-page', 'primer-probability.html')]:
        report = OUT / f'browser34-source90-{kind}-v1.json'
        artifacts = OUT / f'browser34-source90-{kind}-artifacts-v1'
        assert not report.exists() and not artifacts.exists()
        commands.append((kind, ['node', 'qa/learning_review.mjs', '--report', str(report.relative_to(ROOT)),
                               '--artifacts', str(artifacts.relative_to(ROOT)), page], report))
    region_report = OUT / 'browser34-source90-five-changed-regions-v1.json'
    commands.append(('five-changed-regions-and-two-scalar-trajectories', ['node', str((OUT / 'source90_changed_regions_and_scalar_finite34_v1.mjs').relative_to(ROOT))], region_report))

    def run(item):
        kind, command, report = item
        assert guard() == []
        started, tick = datetime.now(timezone.utc).isoformat(), time.monotonic()
        log = OUT / f'browser34-source90-{kind}-actual-v1.log'
        with log.open('xb') as stream:
            native = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        finished, elapsed = datetime.now(timezone.utc).isoformat(), time.monotonic() - tick
        errors = guard()
        record = {'status': 'passed' if native.returncode == 0 and not errors else 'failed',
                  'actual_exit_code': native.returncode, 'actual_command': command, 'actual_workdir': str(ROOT),
                  'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': elapsed,
                  'raw_log': ref(log), 'protected_baseline': ref(baseline_path), 'protected_file_changes': errors,
                  'browser_report': ref(report) if report.exists() else None, 'recorder': ref(Path(__file__)),
                  'site_or_canonical_proof_mutations': False, 'coverage_complete': False}
        path = OUT / f'browser34-source90-{kind}-actual-v1.json'
        assert not path.exists()
        path.write_text(json.dumps(record, indent=2) + '\n')
        print(json.dumps({'kind': kind, 'status': record['status'], 'actual_exit_code': native.returncode,
                          'elapsed_seconds': elapsed, 'actual_record': ref(path), 'protected_file_changes': errors}), flush=True)
        return {'kind': kind, 'actual_record': ref(path), 'actual_exit_code': native.returncode, 'report': record['browser_report']}

    records = []
    with ThreadPoolExecutor(max_workers=3) as executor:
        futures = [executor.submit(run, item) for item in commands]
        for future in as_completed(futures):
            records.append(future.result())
    errors = guard()
    passed = len(records) == 3 and all(row['actual_exit_code'] == 0 for row in records) and not errors
    summary_path.write_text(json.dumps({'status': 'passed_actual_Source90_three_browser_commands_visual_review_pending' if passed else 'failed_actual_Source90_browser_commands',
        'completed_at_utc': datetime.now(timezone.utc).isoformat(), 'actual_execution_count': len(records), 'actual_records': records,
        'protected_baseline': ref(baseline_path), 'protected_file_changes': errors, 'visualInspection': 'pending',
        'coverage_complete': False}, indent=2) + '\n')
    print(json.dumps({'execution_summary': ref(summary_path), 'passed': passed}), flush=True)
    if not passed:
        sys.exit(1)


if __name__ == '__main__':
    main()
