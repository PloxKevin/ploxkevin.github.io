"""Hold actual corrected65 bytes for new builds; audit28 retains Source60."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
OLD=Path('/tmp/root_tmp_lean_current64_owner28_context_v1.json')
OLD_RUNNER=Path('/tmp/root_tmp_lean_current64_owner28_runner_v1.py')
NEW=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
RUNNER=Path('/tmp/root_tmp_lean_current65_owner28_runner_v1.py')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_bytes())
def ref(p):return {'file':str(p),'sha256':sha(p)}
assert sha(OLD)=='442590b45444a97af4b12a37b9ee3f6166b6118a85516e339c6d55bb0c33c6e0'
assert sha(OLD_RUNNER)=='4c092cb65529bfd8a59b42bf04aae743c09241507e7bad6f732d12204cb437d6'
assert not NEW.exists() and not RUNNER.exists()
application=ROOT/'reports/full-coverage/source65-correction-application-v1.json'
native=ROOT/'reports/full-coverage/source65-correction-application29-execution-v1.json'
a=read(application);n=read(native)
assert a['status']=='passed_actual_source65_correction_full29_inventory_owner_identity_rebase_pending'
assert n['status']=='passed' and type(n['actual_exit_code']) is int and n['actual_exit_code']==0
assert sha(ROOT/n['log'])==n['log_sha256']
assert n['actual_command']==['python3','book/coverage/checks/root_apply_source65_v1.py','--peer','book/coverage/checks/future28-foundations/source65-independent-foundations29-v1/source65-narrow-wording-proof-support-full29-parser-independent-foundations29-peer-v1.json','--peer-sha256','171c17c88f5c1f6a53bce11b38f3dca0a4f03f4019b48be69f8c5e5350151c70','--apply']
assert a['source_after']['file']=='SafeLearning/lipsdp.html' and sha(ROOT/a['source_after']['file'])==a['source_after']['sha256']
assert len(read(ROOT/'book/coverage/material-corrections.json')['corrections'])==65
context=read(OLD); changed={a['source_after']['file']:a['source_after']['sha256']}
for name,h in context['held_current_source_sha256'].items():assert sha(ROOT/name)==changed.get(name,h),name
context['held_current_source_sha256'].update(changed)
for name in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/inventory-after-correction65.json']:
    context['pins_sha256'][name]=sha(ROOT/name)
for p in [application,native,ROOT/n['log']]:context['pins_sha256'][p.relative_to(ROOT).as_posix()]=sha(p)
for name,h in context['pins_sha256'].items():assert sha(ROOT/name)==h,name
for name,h in context['owners_sha256'].items():assert sha(ROOT/name)==h,name
inventory=read(ROOT/'book/coverage/inventory.json');assert all(context['held_current_source_sha256'][name]==h for name,h in inventory['source_sha256'].items())
context.update(status='actual_current65_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only',prepared_at_utc=datetime.now(timezone.utc).isoformat(),original_source64_context=ref(OLD),original_source64_runner=ref(OLD_RUNNER),actual_source65_application=ref(application),actual_source65_application_native=ref(native),scope='Actual Source65 lesson/inventory/correction bytes, all1186 unchanged audited28 proof sources and five exact owner28 ledgers are held. The published/frozen checkpoint28 audit remains evidence for its original Source60 inputs. New executions do not relabel any old receipt or claim owner rebasing, new selection or new aggregate/axiom audit.',coverage_complete=False)
with NEW.open('xb') as f:f.write((json.dumps(context,indent=2)+'\n').encode())
text=OLD_RUNNER.read_text().replace(str(OLD),str(NEW)).replace(sha(OLD),sha(NEW))
text=text.replace('actual_current64_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only','actual_current65_owner28_context_after_reviewed_source_corrections_for_new_tmp_trials_only')
text=text.replace('corrected Source64','corrected Source65').replace('actual_source64_installed28_context','actual_source65_installed28_context').replace('unchanged_current64_book_assets','unchanged_current65_book_assets')
assert str(OLD) not in text and sha(OLD) not in text
with RUNNER.open('x') as f:f.write(text)
assert sha(OLD)=='442590b45444a97af4b12a37b9ee3f6166b6118a85516e339c6d55bb0c33c6e0'
assert sha(OLD_RUNNER)=='4c092cb65529bfd8a59b42bf04aae743c09241507e7bad6f732d12204cb437d6'
print(json.dumps({'status':context['status'],'new_context':ref(NEW),'new_runner':ref(RUNNER),'coverage_complete':False}))
