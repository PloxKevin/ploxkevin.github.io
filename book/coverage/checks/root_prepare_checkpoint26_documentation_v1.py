"""Document actual checkpoint26 checks, retaining the completed25 delivery."""
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
    d=read(name)
    values=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert values and all(type(x) is int and x==0 for x in values)
    logs=[d[k] for k in ('log','raw_log') if k in d]
    hashes=[d[k] for k in ('log_sha256','raw_log_sha256') if k in d]
    assert logs and hashes and all(x==logs[0] for x in logs) and all(x==hashes[0] for x in hashes)
    assert sha(logs[0])==hashes[0]
    return d

audit_name='reports/full-coverage/lean-checkpoint-26/verification-original.json'
ledger_name='reports/full-coverage/lean-checkpoint-26/ledger-audit.json'
manifest_name='reports/full-coverage/checkpoint-26-manifest.json'
selection_name='reports/full-coverage/checkpoint-26-selection.json'
audit,ledger,manifest,selection=map(read,(audit_name,ledger_name,manifest_name,selection_name))
assert audit['status']=='passed' and audit['proof_file_count']==1167 and audit['theorem_count']==9503
assert all(type(c['exit_code']) is int and c['exit_code']==0 for c in audit['checks'])
fresh=sum(c.get('evidence_mode')=='fresh_kernel_replay' for c in audit['checks'])
reuse=sum(c.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for c in audit['checks'])
assert (fresh,reuse)==(11,1156)
assert manifest['status']=='formal_verification_passed_partial_coverage'
assert manifest['selection_sha256']==sha(selection_name) and manifest['proof_files']==selection['proof_files']
assert audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()}
assert audit['lean_version'].startswith('Lean (version 4.34.1,')
assert audit['mathlib_revision']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9503
assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(xs)<=set(audit['allowed_standard_axioms']) for xs in audit['axiom_dependencies'].values())
assert audit['checks'][-1]['command']==['lake','env','lean',str(ROOT/'reports/full-coverage/checkpoint-26/verification/lean/AxiomAudit.lean')]
assert 'evidence_mode' not in audit['checks'][-1]
assert manifest['successful_verification']['report_sha256']==sha(audit_name)
assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
assert ledger['inventory_sha256']==sha('book/coverage/inventory.json')==sha('book/coverage/inventory-after-correction53.json')=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
assert len(read('book/coverage/material-corrections.json')['corrections'])==53
content_ref=selection['previous_frozen_input_content_binding']
assert sha(content_ref['file'])==content_ref['sha256']
binding=read(content_ref['file']);assert binding['original_input_count']==44111
prior=read('reports/full-coverage/checkpoint-25-manifest.json')
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
old_assets={n:h for n,h in prior['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31 and assets.keys()==old_assets.keys()
assert {n for n in assets if assets[n]!=old_assets[n]}=={'SafeLearning/lyapunov-mpc.html'}
for n,h in assets.items():assert sha(n)==h
browser_name='reports/full-coverage/browser-checkpoint-26.json';browser=read(browser_name)
assert browser['status']=='passed_actual_changed_pages_and_exact_unchanged_evidence'
assert browser['source_sha256']==assets
for n,h in browser['qa_source_sha256'].items():assert sha(n)==h
assert (browser['verified_viewport_count'],browser['fresh_verified_viewport_count'],browser['retained_verified_viewport_count'])==(145,5,140)
assert (browser['screenshot_count'],browser['skipped_capture_target_count'])==(48,10)
assert browser['manual_visual_inspection']['status']=='whole_48_capture_manual_review_remains_pending'
static_name='reports/full-coverage/integration-26.json';static=read(static_name)
assert static['status']=='PASS' and static['errors']==[]
assert static['counts']['html_pages']==29 and static['counts']['all_current_exercises']==556
closed={}
for stem in ('verify-checkpoint26-execution-v1','export-checkpoint26-execution-v1','frozen-ledger-checkpoint26-execution-v1','static-checkpoint26-execution-v1'):
    n='reports/full-coverage/'+stem+'.json';d=actual(n)
    closed[n]=sha(n);closed[d.get('log',d.get('raw_log'))]=d.get('log_sha256',d.get('raw_log_sha256'))
integration_name='reports/full-coverage/owner26-reviewed-candidate-integration-v1.json';integration=read(integration_name)
assert integration['applied'] is True and len(integration['exact_replacements'])==5
for r in integration['exact_replacements']:assert sha(r['destination'])==sha(r['candidate']['file'])==r['candidate']['sha256']
counts=ledger['counts'];states=counts['statuses'];materials=counts['material_review_statuses']
assert counts['exercises']==556 and counts['material_source_units']==12774
excounts={label:states.get('exercise:'+key,0) for label,key in [('complete','complete_math'),('partial','partial'),('pending','pending')]}
assert sum(excounts.values())==556 and sum(materials.values())==12774
original=read('book/coverage/progress.json')
backup='reports/full-coverage/progress-checkpoint26-before-preparation-original-v1.json'
readme_backup='reports/full-coverage/README-checkpoint26-before-preparation-original-v1.md'
report='reports/full-coverage/progress-checkpoint26-preparation-update-v1.json'
assert all(not safe(n).exists() for n in (backup,readme_backup,report))
with safe(backup).open('xb') as f:f.write(safe('book/coverage/progress.json').read_bytes())
with safe(readme_backup).open('xb') as f:f.write(safe('reports/full-coverage/README.md').read_bytes())
progress=copy.deepcopy(original)
progress.update(inventory_sha256=ledger['inventory_sha256'],inventory_counts=read('book/coverage/inventory.json')['counts'],
    verified_checkpoint={'proof_files':1167,'theorems':9503,'status':'passed','coverage_complete':False,'report':audit_name,'actual_audit_workdir':str(ROOT/'reports/full-coverage/checkpoint-26/verification/lean')},
    current_frozen_audit={'snapshot':'reports/full-coverage/checkpoint-26','proof_files':1167,'status':'passed_actual_build_kernel_and_axiom_audit'},
    publication_status='checkpoint26_actual_audit_passed_prepared_awaiting_actual_pages_and_live_checks',
    live_delivery_status='checkpoint26_awaiting_actual_pages_and_live_checks',live_delivery_evidence=None,
    current_documented_material_corrections=53,
    working_coverage_report='reports/full-coverage/root-source53-final-owner-integration26-v1.json',
    current_published_ledger_candidate='reports/full-coverage/publication-checks/ledger-checkpoint-26.json')
progress['previous_checkpoint25_delivery']={'entire_original_progress':ref(backup),'content_commit':original['last_published_content_commit'],'live_evidence':original['live_delivery_evidence'],'publication_status':original['publication_status']}
progress['working_next_checkpoint_preparation']={'status':'checkpoint26_actual_frozen_audit_passed_delivery_pending','coverage_complete':False,
    'inventory':'book/coverage/inventory-after-correction53.json','expected_proof_files':1167,'expected_public_theorems':9503,
    'exercise_counts':excounts,'material_review_units':materials,'integration_execution':'reports/full-coverage/owner26-integration-apply-execution-v1.json',
    'global_integrity':'reports/full-coverage/root-source53-final-owner-integration26-v1.json'}
safe('book/coverage/progress.json').write_text(json.dumps(progress,indent=2)+'\n')
text=f"""# Continuing full mathematical coverage

Checkpoint 26 passed the actual Lean 4.34.1 build, kernel and axiom audit:
9,503 public theorems in 1,167 selected files. [The original audit](lean-checkpoint-26/verification-original.json)
and [its measured execution](verify-checkpoint26-execution-v1.json) retain actual commands and times.
The 11 additions received fresh kernel replays; the 1,156 earlier files retain their
successful replays after exact source, transitive import and dependency fingerprints matched.
Every indexed theorem received a fresh axiom audit.

Coverage remains partial: {excounts['complete']} of 556 exercises are complete,
{excounts['partial']} partial and {excounts['pending']} pending. Of 12,774 overlapping
material units, {materials['reviewed']:,} are reviewed and {materials['pending']:,} pending.
[The frozen ledger](lean-checkpoint-26/ledger-audit.json) checks literal fingerprints
and selected declarations. Independent reviews establish source correspondence;
Lean certifies the encoded statements.

The additions cover metric and isometry arguments, conditional distributions,
the scalar convex scenario exercise, wind-model classifications, fractional CVaR
selectors and randomized Gaussian smoothing. MPC components prove safety and
convergence for an explicitly switched controller under stated premises; deriving
the general robust replanning certificate remains an open obligation.

Source53 clarifies finite terminal-set entry, pre-entry controller error bounds
and the scenario theorem's unique original-objective minimizers. [Static checks](integration-26.json)
passed on all 29 pages and 556 exercises. [Browser evidence](browser-checkpoint-26.json)
contains five fresh viewport checks for the changed page and 140 retained checks
for 28 unchanged pages after exact page and QA hashes matched. It includes 48
application captures and ten explicitly skipped targets. Six changed paragraph
captures were inspected; whole-site manual screenshot review remains pending.

[The manifest](checkpoint-26-manifest.json) binds {len(manifest['frozen_inputs_sha256']):,} frozen inputs.
[The selection](checkpoint-26-selection.json) preserves all 1,156 prior proof sources.
Exact content bindings retain every original checkpoint25 path and byte hash.
Original semantic bodies, hypotheses, commands, failed and passing outputs, and
times remain unchanged. Checkpoint25's completed GitHub Pages delivery is preserved
in the progress history. Checkpoint26 awaits its own actual push, Pages build and live checks.

Complete audit archives and [Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
remain in Git. Reproduce checks into new output paths:

```sh
python3 book/validate.py --allow-reviewed-corrections --output reports/full-coverage/integration-reproduction26.json
python3 book/coverage/validate.py --output reports/full-coverage/ledger-reproduction26.json
python3 verification/lean/verify.py --output reports/full-coverage/lean-reproduction26
```

The local frozen checkout is `reports/full-coverage/checkpoint-26`. Publication
places selected inputs at their original paths. This checkpoint leaves the full
coverage objective unfinished.
"""
safe('reports/full-coverage/README.md').write_text(text)
out={'status':'passed_actual_checkpoint26_audit_documentation_prepared_delivery_pending',
    'updated_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(str(Path(__file__).relative_to(ROOT))),
    'original_progress':ref(backup),'original_readme':ref(readme_backup),'current_progress':ref('book/coverage/progress.json'),
    'current_readme':ref('reports/full-coverage/README.md'),'actual_audit':ref(audit_name),'actual_frozen_ledger':ref(ledger_name),
    'browser26_report':ref(browser_name),'closed_actual_execution_evidence_sha256':closed,
    'exercise_counts':excounts,'material_review_units':materials,'coverage_complete':False}
with safe(report).open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
