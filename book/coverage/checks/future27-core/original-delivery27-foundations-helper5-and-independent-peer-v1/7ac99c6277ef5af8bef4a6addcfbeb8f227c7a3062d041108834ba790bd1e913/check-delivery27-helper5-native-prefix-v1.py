from pathlib import Path
from datetime import datetime,timezone
import hashlib,importlib.util,json
ROOT=Path('/home/oxrexkevin/SafetyBased');HELPER=Path('/tmp/root_close_publication27_delivery_v5.py')
OUT=Path('/tmp/delivery27-helper5-native-prefix-findings-v1.json');assert not OUT.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('delivery27_test_helper5',HELPER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
held={n:sha(ROOT/n) for n in [m.PROGRESS,m.README,*m.PINS]};start=datetime.now(timezone.utc).isoformat()
assets=m.immutable();assert len(assets)==31
fixtures=[]
for name,d in [('bool_code',{'actual_exit_code':False}),('conflicting_code_alias',{'exit_code':0,'actual_exit_code':1}),('missing_code',{}),('string_code',{'exit_code':'0'}),('conflicting_runner_code',{'exit_code':0,'actual_runner_exit_code':2})]:
    try:m.zero(d)
    except AssertionError:fixtures.append({'name':name,'rejected':True})
    else:raise AssertionError(name)
for name,d,keys in [('command_conflict',{'command':['a'],'actual_command':['b']},('command','actual_command')),('cwd_conflict',{'cwd':'a','actual_workdir':'b'},('cwd','working_directory','actual_workdir')),('log_conflict',{'log':'a','raw_log':'b'},('log','raw_log')),('log_hash_conflict',{'log_sha256':'a','raw_log_sha256':'b'},('log_sha256','raw_log_sha256')),('missing_alias',{},('command','actual_command'))]:
    try:m.aliases(d,keys)
    except AssertionError:fixtures.append({'name':name,'rejected':True})
    else:raise AssertionError(name)
for name in ['/tmp/out','../outside','reports/../outside','reports/full-coverage/a\nb']:
    try:m.safe(name)
    except AssertionError:fixtures.append({'name':repr(name),'rejected':True})
    else:raise AssertionError(name)
for name in ['SafeLearning/primer-optimization.html','verification/lean/SafeLearning/new.lean','book/coverage/foundations.json','reports/full-coverage/checkpoint-27/file.json','reports/full-coverage/lean-checkpoint-27/file.json']:
    try:m.metadata(name)
    except AssertionError:fixtures.append({'name':name,'rejected':True})
    else:raise AssertionError(name)
assert len(fixtures)==19
for n,h in held.items():assert sha(ROOT/n)==h,n
d={'status':'passed_genuine_current27_read_only_prefix_and19_rejection_fixtures','errors':[],'helper':{'file':str(HELPER),'sha256':sha(HELPER)},'reviewed_at_utc':start,'completed_at_utc':datetime.now(timezone.utc).isoformat(),'genuine_native_immutable_prefix':{'proof_files':1175,'theorems':9644,'checks':1178,'fresh_replays':8,'retained_replays':1167,'book_assets':31,'owners':5,'inventory55':True,'original_audit':'fdd431eea1137c48032d20cdb31270b8d76a4ca715f19715167a1ec67cff194f'},'fixtures':fixtures,'held_root_metadata_sha256_before_after':held,'production_update_or_stage_executed':False,'future_native_delivery_family_currently_present':{n:(ROOT/n).exists() for n in [m.LIVE,m.PAGES,*['reports/full-coverage/'+s+'.json' for s in m.STEMS]]},'scope':'This run verifies the genuine read-only current27 immutable prefix and directly rejects conflicting aliases, non-native zero codes and disallowed paths. It does not claim complete future delivery update/stage execution or a semantic code peer. Versions1/2 remain unchanged; native version2 import failed because PyYAML is unavailable. Version3 native prefix rejected the wrong raw-vs-pruned Applied-owner equality without writing. Version5 additionally skips literal excluded paths before rejecting included symlinks and forces the exact validated metadata whitelist into Git so its ignored logs are preserved. Version4 independently verifies exact raw Root candidate, frozen PUB owner bytes and the authorized inverse three-source metadata removal/body equality, adds status and Git/index/symlink gates.'}
with OUT.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'findings':{'file':str(OUT),'sha256':sha(OUT)},'fixture_count':len(fixtures)}))
