"""Bind closed interface/plan evidence in a new pre-selection plan version."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT=Path(__file__).resolve().parents[3]
BASE='book/coverage/checks/future25-core'
OLD=BASE+'/checkpoint25-installed-owner-selection-plan-v1.json'
NEW=BASE+'/checkpoint25-installed-owner-selection-plan-v2.json'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def ref(n):return {'file':n,'sha256':sha(n)}
old=read(OLD)
assert old['status']=='independently_reviewed_installed_owner25_selection_plan'
assert not (ROOT/NEW).exists() and not (ROOT/'reports/full-coverage/checkpoint-25-selection.json').exists()
records=[]
for stem in ['prepare-owner25-interface-request-execution-v1','prepare-owner25-live-interfaces-execution-v1','prepare-owner25-selection-plan-execution-v1']:
    n='reports/full-coverage/'+stem+'.json';d=read(n)
    assert d['actual_exit_code']==0 and sha(d['log'])==d['log_sha256']
    records.extend([n,d['log']])
alias_dir=BASE+'/root-closed-interface-plan-original-bytes25-v1'
assert not (ROOT/alias_dir).exists();(ROOT/alias_dir).mkdir()
aliases=[]
extra=copy.deepcopy(old['additional_frozen_inputs'])
for n in records:
    target=alias_dir+'/'+Path(n).name
    with (ROOT/target).open('xb') as f:f.write((ROOT/n).read_bytes())
    assert sha(target)==sha(n)
    aliases.append({'original':ref(n),'immutable_original_byte_copy':ref(target)})
catalog=BASE+'/root-closed-interface-plan-original-byte-aliases25-v1.json'
with (ROOT/catalog).open('x') as f:f.write(json.dumps({'status':'completed_exact_closed_original_interface_and_plan_execution_byte_aliases','aliases':aliases,'scope':'Original command/time/status/log bodies are unchanged. No new compiler or mathematical execution is inferred.'},indent=2)+'\n')
for p in (ROOT/BASE).rglob('*'):
    if p.is_file() and '__pycache__' not in p.parts and p.suffix in {'.json','.log','.py','.lean','.txt','.cjs'}:
        n=p.relative_to(ROOT).as_posix();digest=sha(n)
        if n in extra:assert extra[n]['sha256']==digest
        else:extra[n]={'sha256':digest,'scope':'immutable_audit_or_local_source_evidence'}
for n in [str(Path(__file__).relative_to(ROOT)),'book/coverage/checks/pages24-config-helper-independent-modules-review-v2.json','book/coverage/checks/future24-core/pages24-config-independent-output-review-v1.json']:
    extra[n]={'sha256':sha(n),'scope':'immutable_audit_or_local_source_evidence'}
for n,row in extra.items():
    assert sha(n)==row['sha256'] and row['sha256'] not in set(old['excluded_full_external_reference_sha256'])
out=copy.deepcopy(old)
out['additional_frozen_inputs']=extra
out['helpers_sha256'][str(Path(__file__).relative_to(ROOT))]=sha(str(Path(__file__).relative_to(ROOT)))
out.update(original_installed_owner_selection_plan_v1=ref(OLD),
    entire_original_installed_owner_selection_plan_v1_body_and_time=old,
    closed_interface_and_plan_original_byte_aliases=ref(catalog),
    plan_closure_prepared_at_utc=datetime.now(timezone.utc).isoformat())
inverse=copy.deepcopy(out)
for k in ['original_installed_owner_selection_plan_v1','entire_original_installed_owner_selection_plan_v1_body_and_time','closed_interface_and_plan_original_byte_aliases','plan_closure_prepared_at_utc']:inverse.pop(k)
inverse['additional_frozen_inputs']=old['additional_frozen_inputs'];inverse['helpers_sha256']=old['helpers_sha256']
assert inverse==old
with (ROOT/NEW).open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'passed_closed_preselection_plan_evidence','plan':ref(NEW),'added_inputs':len(extra)-len(old['additional_frozen_inputs']),'original_plan_entire_inverse_exact':True}))
