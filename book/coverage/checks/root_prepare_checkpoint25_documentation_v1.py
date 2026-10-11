"""Document actual passing25 checks; publication and live delivery remain separate."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json
ROOT=Path(__file__).resolve().parents[3]
def safe(name):
    assert isinstance(name,str) and name
    p=Path(name)
    assert not p.is_absolute() and '..' not in p.parts and str(p)==name
    assert (ROOT/p).resolve().is_relative_to(ROOT.resolve())
    return ROOT/p
def sha(name):return hashlib.sha256(safe(name).read_bytes()).hexdigest()
def read(name):return json.loads(safe(name).read_text())
def ref(name):return {'file':name,'sha256':sha(name)}
def actual(name):
    value=read(name)
    codes=[value[k] for k in ('actual_exit_code','exit_code') if k in value]
    assert codes and all(type(c) is int and c==0 for c in codes)
    logs=[value[k] for k in ('log','raw_log') if k in value]
    hashes=[value[k] for k in ('log_sha256','raw_log_sha256') if k in value]
    assert logs and hashes and all(x==logs[0] for x in logs) and all(x==hashes[0] for x in hashes)
    assert sha(logs[0])==hashes[0]
    return value

audit_name='reports/full-coverage/lean-checkpoint-25/verification-original.json'
ledger_name='reports/full-coverage/lean-checkpoint-25/ledger-audit.json'
manifest_name='reports/full-coverage/checkpoint-25-manifest.json'
selection_name='reports/full-coverage/checkpoint-25-selection.json'
audit,ledger,manifest,selection=map(read,(audit_name,ledger_name,manifest_name,selection_name))
assert audit['status']=='passed' and audit['proof_file_count']==1156 and audit['theorem_count']==9369
assert all(type(c['exit_code']) is int and c['exit_code']==0 for c in audit['checks'])
fresh=sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])
reuse=sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])
assert (fresh,reuse)==(12,1144)
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert manifest['selection_sha256']==sha(selection_name) and manifest['proof_files']==selection['proof_files']
assert audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()}
assert audit['lean_version'].startswith('Lean (version 4.34.1,')
assert audit['mathlib_revision']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9369
assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(values)<=set(audit['allowed_standard_axioms']) for values in audit['axiom_dependencies'].values())
assert audit['checks'][-1]['command']==['lake','env','lean',str(ROOT/'reports/full-coverage/checkpoint-25/verification/lean/AxiomAudit.lean')]
assert 'evidence_mode' not in audit['checks'][-1]
assert manifest['successful_verification']['report_sha256']==sha(audit_name)
assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
assert ledger['inventory_sha256']==sha('book/coverage/inventory.json')==sha('book/coverage/inventory-after-correction52.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
content_ref=selection['previous_frozen_input_content_binding']
assert sha(content_ref['file'])==content_ref['sha256']
binding=read(content_ref['file']);assert binding['original_input_count']==40485
prior_manifest=read('reports/full-coverage/checkpoint-24-manifest.json')
current_assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
prior_assets={n:h for n,h in prior_manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(current_assets)==31 and current_assets==prior_assets
for n,h in current_assets.items():assert sha(n)==h
# This explicitly retains the completed24 browser evidence; it is not a fresh25 run.
browser_name='reports/full-coverage/browser-checkpoint-24.json';browser=read(browser_name)
assert browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence'
assert browser['source_sha256']==current_assets
for n,h in browser['qa_source_sha256'].items():assert sha(n)==h
assert (browser['verified_viewport_count'],browser['fresh_verified_viewport_count'],browser['retained_verified_viewport_count'])==(145,5,140)
assert (browser['screenshot_count'],browser['skipped_capture_target_count'])==(48,10)
static_name='reports/full-coverage/integration-25.json';static=read(static_name)
assert static['status']=='PASS' and static['errors']==[]
assert static['counts']['html_pages']==29 and static['counts']['all_current_exercises']==556
closed={}
for stem in ('verify-checkpoint25-execution-v1','export-checkpoint25-execution-v1','frozen-ledger-checkpoint25-execution-v1','static-checkpoint25-execution-v1'):
    n='reports/full-coverage/'+stem+'.json';record=actual(n)
    closed[n]=sha(n);closed[record.get('log',record.get('raw_log'))]=record.get('log_sha256',record.get('raw_log_sha256'))
counts=ledger['counts'];states=counts['statuses'];materials=counts['material_review_statuses']
assert counts['exercises']==556 and counts['material_source_units']==12774
exercise_counts={label:states.get('exercise:'+key,0) for label,key in [('complete','complete_math'),('partial','partial'),('pending','pending')]}
assert sum(exercise_counts.values())==556 and sum(materials.values())==12774
integration_name='reports/full-coverage/owner25-reviewed-candidate-integration-v1.json'
integration=read(integration_name)
assert integration['applied'] is True
assert integration['status']=='four_exact_reviewed_owner25_candidate_bytes_integrated_pending_fresh_global_integrity_and_aggregate25_audit'
assert integration['all40485_frozen24_inputs_exact'] is True and integration['all1144_selected24_root_source_hashes_exact'] is True
assert set(integration['authorized_current_future_code_updates'])=={'book/coverage/checks/run_root_barrier_control25_canonical_pair_v1.py'}
for n,h in integration['authorized_current_future_code_update_reference_sha256'].items():assert sha(n)==h
for r in integration['exact_replacements']:assert sha(r['destination'])==sha(r['candidate']['file'])==r['candidate']['sha256']
original=read('book/coverage/progress.json')
backup='reports/full-coverage/progress-checkpoint25-before-preparation-original-v1.json'
readme_backup='reports/full-coverage/README-checkpoint25-before-preparation-original-v1.md'
report='reports/full-coverage/progress-checkpoint25-preparation-update-v1.json'
for n in (backup,readme_backup,report):assert not safe(n).exists()
with safe(backup).open('xb') as out:out.write(safe('book/coverage/progress.json').read_bytes())
with safe(readme_backup).open('xb') as out:out.write(safe('reports/full-coverage/README.md').read_bytes())
progress=copy.deepcopy(original)
progress.update(inventory_sha256=ledger['inventory_sha256'],inventory_counts=read('book/coverage/inventory.json')['counts'],
    verified_checkpoint={'proof_files':1156,'theorems':9369,'status':'passed','coverage_complete':False,
        'report':audit_name,'actual_audit_workdir':str(ROOT/'reports/full-coverage/checkpoint-25/verification/lean')},
    current_frozen_audit={'snapshot':'reports/full-coverage/checkpoint-25','proof_files':1156,'status':'passed_actual_build_kernel_and_axiom_audit'},
    publication_status='checkpoint25_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks',
    live_delivery_status='checkpoint25_awaiting_actual_pages_and_live_checks',live_delivery_evidence=None,
    current_documented_material_corrections=52,
    working_coverage_report='reports/full-coverage/root-source52-final-owner-integration25-v1.json',
    current_published_ledger_candidate='reports/full-coverage/publication-checks/ledger-checkpoint-25.json')
progress['previous_checkpoint24_delivery']={'entire_original_progress':ref(backup),
    'content_commit':original['last_published_content_commit'],'live_evidence':original['live_delivery_evidence'],
    'publication_status':original['publication_status']}
progress['working_next_checkpoint_preparation']={'status':'checkpoint25_actual_frozen_audit_passed_delivery_pending',
    'coverage_complete':False,'inventory':'book/coverage/inventory-after-correction52.json',
    'expected_proof_files':1156,'expected_public_theorems':9369,'exercise_counts':exercise_counts,
    'material_review_units':materials,'integration_execution':'reports/full-coverage/owner25-integration-apply-execution-v1.json',
    'global_integrity':'reports/full-coverage/root-source52-final-owner-integration25-v1.json'}
safe('book/coverage/progress.json').write_text(json.dumps(progress,indent=2)+'\n')
text=f"""# Continuing full mathematical coverage

Checkpoint 25 passed the actual Lean 4.34.1 build, kernel and axiom audit:
9,369 public theorems in 1,156 selected files. [The original audit](lean-checkpoint-25/verification-original.json)
and [its measured execution](verify-checkpoint25-execution-v1.json) retain the actual commands and times.
The 12 additions received fresh kernel replays; the 1,144 earlier files reuse their
original successful replays only after exact source, transitive import and dependency
fingerprints matched. Every indexed theorem received a fresh axiom audit.

Coverage remains partial: {exercise_counts['complete']} of 556 exercises are complete,
{exercise_counts['partial']} partial and {exercise_counts['pending']} pending.
Of 12,774 overlapping material units, {materials['reviewed']:,} are reviewed and
{materials['pending']:,} remain pending. [The frozen-ledger check](lean-checkpoint-25/ledger-audit.json)
checks exact literal fingerprints and selected declarations. Independent reviews establish
source correspondence; Lean checks certify the encoded statements.

The new proofs cover a barrier-control example, the quadratic twenty-point grid,
scalar calculus, Gaussian models and conditioning, and precise temporal multiplier
components. The corrected shifted-tanh answer(b) has a complete source review with
selected universal order lemmas. The three temporal components retain their exact
hypotheses. The whole answer(c) and neural-network exercise remain unfinished.

The Source52 website assets are byte-identical to checkpoint24. [Static validation](integration-25.json)
passed on all 29 pages and 556 exercises. [The retained browser report](browser-checkpoint-24.json)
records 145 earlier viewport checks, 48 screenshots and ten explicit skipped captures.
All 31 site-asset hashes and both QA helper hashes match. These are retained checks,
not a new browser run or a new Pages deployment.

[The manifest](checkpoint-25-manifest.json) binds {len(manifest['frozen_inputs_sha256']):,} frozen inputs.
[The selection](checkpoint-25-selection.json) preserves all 1,144 earlier proof sources
and their ordinary evidence. Exact content bindings retain every one of the 40,485
checkpoint24 paths and hashes with {binding['new_unique_snapshot_alias_count']:,} new unique aliases.
Four historical owner-evidence paths use the genuine archived prior bytes, with entire
original rows retained. One independently reviewed future preparation helper gained
four archive patterns after its unexecuted draft was frozen; its old snapshot and
actual first-run bytes are both preserved under Root's exact single-file authorization.
Original semantic bodies, hypotheses, commands, failed/passing outputs and times remain unchanged.

Checkpoint25 has passed the local audit and awaits an actual GitHub Pages build and
live asset checks. Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Full external references retain their separate attribution scope.

From the published repository root, reproduce checks into NEW output paths:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction25.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction25.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction25
```

The local frozen checkout is `reports/full-coverage/checkpoint-25`; publication places
selected inputs at their original paths. Kernel reuse requires exact matching saved
fingerprints. This checkpoint does not complete the coverage objective.
"""
safe('reports/full-coverage/README.md').write_text(text)
out={'status':'passed_actual_checkpoint25_audit_documentation_prepared_delivery_pending',
    'updated_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(str(Path(__file__).relative_to(ROOT))),
    'original_progress':ref(backup),'original_readme':ref(readme_backup),
    'current_progress':ref('book/coverage/progress.json'),'current_readme':ref('reports/full-coverage/README.md'),
    'actual_audit':ref(audit_name),'actual_frozen_ledger':ref(ledger_name),
    'retained_browser24_report':ref(browser_name),'retained_browser_scope':'Exact unchanged31 site assets and QA helpers; no fresh25 browser execution inferred.',
    'closed_actual_execution_evidence_sha256':closed,'exercise_counts':exercise_counts,
    'material_review_units':materials,'coverage_complete':False}
with safe(report).open('x') as out_file:out_file.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
