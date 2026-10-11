"""Describe the actual passing24 audit while delivery still awaits Pages/live."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT=Path(__file__).resolve().parents[3]
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
audit=read('reports/full-coverage/lean-checkpoint-24/verification-original.json')
ledger=read('reports/full-coverage/lean-checkpoint-24/ledger-audit.json')
manifest=read('reports/full-coverage/checkpoint-24-manifest.json')
selection=read('reports/full-coverage/checkpoint-24-selection.json')
assert audit['status']=='passed' and audit['proof_file_count']==1144 and audit['theorem_count']==9279
assert all(c['exit_code']==0 for c in audit['checks'])
fresh=sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])
reuse=sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])
assert (fresh,reuse)==(13,1131)
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
assert ledger['inventory_sha256']==sha('book/coverage/inventory.json')==sha('book/coverage/inventory-after-correction52.json')
assert manifest['selection_sha256']==sha('reports/full-coverage/checkpoint-24-selection.json')
assert manifest['proof_files']==selection['proof_files']
assert audit['proof_sha256']=={name:row['sha256'] for name,row in selection['proof_files'].items()}
assert audit['lean_version'].startswith('Lean (version 4.34.1,')
assert audit['mathlib_revision']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9279
assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(values)<=set(audit['allowed_standard_axioms']) for values in audit['axiom_dependencies'].values())
assert audit['checks'][-1]['command']==['lake','env','lean',str(ROOT/'reports/full-coverage/checkpoint-24/verification/lean/AxiomAudit.lean')] and 'evidence_mode' not in audit['checks'][-1]
binding=read(selection['previous_frozen_input_content_binding']['file'])
assert sha(selection['previous_frozen_input_content_binding']['file'])==selection['previous_frozen_input_content_binding']['sha256']
assert binding['original_input_count']==36910
static=read('reports/full-coverage/integration-24.json')
assert static['status']=='PASS' and static['errors']==[]
assert static['counts']['html_pages']==29 and static['counts']['all_current_exercises']==556
browser=read('reports/full-coverage/browser-checkpoint-24.json')
assert browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence'
assert (browser['verified_viewport_count'],browser['fresh_verified_viewport_count'],browser['retained_verified_viewport_count'])==(145,5,140)
assert (browser['screenshot_count'],browser['skipped_capture_target_count'])==(48,10)
manual=read('book/coverage/checks/future24-core/root24-corrected-NN-paragraphs-manual-visual-inspection-v1.json')
assert manual['status']=='manual_inspection_completed_for_four_actual_corrected_NN_paragraph_captures' and len(manual['images_sha256'])==4
for name,digest in manual['images_sha256'].items():assert sha(name)==digest
for name,digest in manual['actual_capture_evidence'].items():assert sha(name)==digest
assert manual['source_sha256']['SafeLearning/nn-in-the-loop.html']==sha('SafeLearning/nn-in-the-loop.html')
for name in ['verify-checkpoint24-execution-v1','export-checkpoint24-execution-v1','frozen-ledger-checkpoint24-execution-v1',
    'static-checkpoint24-execution-v1','browser-source52-24-runner-execution-v1','browser-checkpoint24-binding-execution-v1',
    'source52-corrected-paragraphs24-capture-execution-v2']:
    actual=read('reports/full-coverage/'+name+'.json')
    assert actual['actual_exit_code']==0 and sha(actual['log'])==actual['log_sha256']
assert manifest['successful_verification']['report_sha256']==sha('reports/full-coverage/lean-checkpoint-24/verification-original.json')
counts=ledger['counts'];states=counts['statuses'];materials=counts['material_review_statuses']
assert counts['exercises']==556 and counts['material_source_units']==12774
exercise_counts={name:states.get('exercise:'+key,0) for name,key in [('complete','complete_math'),('partial','partial'),('pending','pending')]}
assert sum(exercise_counts.values())==556 and sum(materials.values())==12774
original=read('book/coverage/progress.json')
backup='reports/full-coverage/progress-checkpoint24-before-preparation-original-v1.json'
readme_backup='reports/full-coverage/README-checkpoint24-before-preparation-original-v1.md'
report='reports/full-coverage/progress-checkpoint24-preparation-update-v1.json'
for n in [backup,readme_backup,report]:assert not (ROOT/n).exists()
with (ROOT/backup).open('xb') as f:f.write((ROOT/'book/coverage/progress.json').read_bytes())
with (ROOT/readme_backup).open('xb') as f:f.write((ROOT/'reports/full-coverage/README.md').read_bytes())
progress=copy.deepcopy(original)
progress.update(inventory_sha256=ledger['inventory_sha256'],inventory_counts=read('book/coverage/inventory.json')['counts'],
    verified_checkpoint={'proof_files':1144,'theorems':9279,'status':'passed','coverage_complete':False,
        'report':'reports/full-coverage/lean-checkpoint-24/verification-original.json','actual_audit_workdir':str(ROOT/'reports/full-coverage/checkpoint-24/verification/lean')},
    current_frozen_audit={'snapshot':'reports/full-coverage/checkpoint-24','proof_files':1144,'status':'passed_actual_build_kernel_and_axiom_audit'},
    publication_status='checkpoint24_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks',
    live_delivery_status='checkpoint24_awaiting_actual_pages_and_live_checks',
    live_delivery_evidence=None,current_documented_material_corrections=52,
    working_coverage_report='reports/full-coverage/root-source52-final-owner-integration24-v1.json',
    current_published_ledger_candidate='reports/full-coverage/publication-checks/ledger-checkpoint-24.json')
progress['previous_checkpoint23_delivery']={'entire_original_progress':ref(backup),
    'content_commit':original['last_published_content_commit'],'live_evidence':original['live_delivery_evidence'],
    'publication_status':original['publication_status']}
progress['working_next_checkpoint_preparation']={'status':'checkpoint24_actual_frozen_audit_passed_delivery_pending_future25_isolated_candidates_in_progress',
    'coverage_complete':False,'inventory':'book/coverage/inventory-after-correction52.json',
    'expected_proof_files':1144,'expected_public_theorems':9279,'exercise_counts':exercise_counts,
    'material_review_units':materials,'integration_execution':'reports/full-coverage/owner24-integration-apply-execution-v1.json',
    'global_integrity':'reports/full-coverage/root-source52-final-owner-integration24-v1.json'}
(ROOT/'book/coverage/progress.json').write_text(json.dumps(progress,indent=2)+'\n')
text=f"""# Continuing full mathematical coverage

Checkpoint 24 passed the actual system Lean 4.34.1 build, kernel and axiom audit:
9,279 public theorems in 1,144 selected files. See [the original formal audit](lean-checkpoint-24/verification-original.json)
and [its measured execution](verify-checkpoint24-execution-v1.json).
The 13 additions received fresh kernel replays. The other 1,131 retain their
original passing replays after exact module, transitive local import, Lean version
and dependency fingerprints matched. Every indexed theorem received a fresh
axiom audit. Original commands, directories, outputs and times remain preserved.

Coverage remains partial: {exercise_counts['complete']} of 556 exercises are complete,
{exercise_counts['partial']} partial and {exercise_counts['pending']} pending.
Of 12,774 overlapping material review units, {materials['reviewed']:,} are reviewed
and {materials['pending']:,} remain pending. [The actual frozen-ledger check](lean-checkpoint-24/ledger-audit.json)
checks literal fingerprints and selected declarations. Independent reviews establish
specific mathematical correspondence; successful Lean checks certify the encoded statements.

The source52 book records 52 teaching corrections. The new neural-network text
uses approximate decimal values and distinguishes an invalid universal QC premise
from the final stability conclusion. Temporal multiplier assumptions and the
additional oddness requirement are explicit. New proofs cover shifted tanh,
the concrete counterexample, sector bounds and zero equilibria. The general
temporal claims and the full neural-network exercise remain unfinished.
Other additions cover the scalar barrier introductory example, orthonormal bases,
coercivity, extreme-value counterexamples, convergence rates and finite/countable
mixture formulas. The Gaussian-mixture worked example remains only partly reviewed.
Isolated future25 work adds no coverage to this checkpoint.

[Static validation](integration-24.json) passed on all 29 pages and 556 exercises.
[Browser evidence](browser-checkpoint-24.json) records five fresh viewport checks
on the corrected neural-network page and 140 earlier checks retained after exact
source and QA helper fingerprints matched. There are 145 checks, 48 standard
screenshots and ten explicit skipped captures. Four additional captures show
the corrected answer paragraphs at phone and desktop widths; a limited manual
inspection found readable prose and mathematics. It does not certify all pages.

[The manifest](checkpoint-24-manifest.json) binds {len(manifest['frozen_inputs_sha256']):,} frozen inputs.
[The selection](checkpoint-24-selection.json) preserves all 1,131 earlier proof
sources and their ordinary evidence. Exact content bindings retain all 36,910
checkpoint23 input paths and hashes with {binding['new_unique_snapshot_alias_count']:,} new unique aliases.
Four historical owner-evidence paths use their genuine archived prior bytes.
The original baseline row bodies, semantic reviews, hypotheses, times and real
failed/passing executions remain preserved. Full external references retain
their separate attributed reference scope.

Checkpoint 24 has passed its local audit and awaits an actual GitHub Pages build
and live asset checks. Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Literal archival exclusions retain the current book, partial ledgers
and both current24 and baseline23 audit reports in the website build.

From the published repository root, reproduce checks into NEW output paths:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction24.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction24.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction24
```

The local frozen checkout is `reports/full-coverage/checkpoint-24`; the Git
publication places selected inputs at their original paths. Use kernel reuse
only with matching saved fingerprints. The remaining material and exercise
claims, exact assumptions, system Lean verification and GitHub delivery remain
part of the continuing objective. This checkpoint does not complete it.
"""
(ROOT/'reports/full-coverage/README.md').write_text(text)
out={'status':'passed_actual_checkpoint24_audit_documentation_prepared_delivery_pending',
    'updated_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(str(Path(__file__).relative_to(ROOT))),
    'original_progress':ref(backup),'original_readme':ref(readme_backup),
    'current_progress':ref('book/coverage/progress.json'),'current_readme':ref('reports/full-coverage/README.md'),
    'actual_audit':ref('reports/full-coverage/lean-checkpoint-24/verification-original.json'),
    'actual_frozen_ledger':ref('reports/full-coverage/lean-checkpoint-24/ledger-audit.json'),
    'exercise_counts':exercise_counts,'material_review_units':materials,'coverage_complete':False}
with (ROOT/report).open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
