from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');H=R/'book/coverage/checks/root_copy_applied27_identity_v2.py';OLD=R/'book/coverage/checks/root_copy_applied27_identity_v1.py';O=Path('/tmp/root-applied27-identity-copy2-independent-modules-review-v1.json');assert not O.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(H)=='753188839a92ce359e079d7f93701ecb7cbc3a5626cc59a6c859a23527d4090f'
s=H.read_text();old=OLD.read_text();normalized=s.replace("assert actual['helper_sha256_before']==actual['helper_sha256_after']\nassert actual['actual_workdir']==str(ROOT)\nassert sha(Path(actual['raw_log']))==actual['raw_log_sha256']", "assert sha(Path(actual['log']))==actual['log_sha256']")
assert normalized==old
tr=ast.parse(s);prefix=[]
for n in tr.body:
 if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and n.value.func.attr=='mkdir' and isinstance(n.value.func.value,ast.Name) and n.value.func.value.id=='BASE':break
 prefix.append(n)
env={'__file__':str(H),'__name__':'independent_read_only_copy_preflight'};exec(compile(ast.Module(body=prefix,type_ignores=[]),str(H),'exec'),env)
assert env['old']['proof_files']=={} and len(env['pack']['original_closed_byte_aliases'])==44 and len(env['pack']['unchanged_root_evidence_sha256'])==150
assert not env['BASE'].exists();aliases={}
for original,r in env['originals'].items():
 p=env['checked'](r);dest=env['BASE']/'original-closed-bytes'/r['sha256']/p.name
 aliases[original]={'file':dest.relative_to(R).as_posix(),'sha256':r['sha256']}
env['aliases']=aliases
canon=next(n for n in tr.body if isinstance(n,ast.FunctionDef) and n.name=='canon');exec(compile(ast.Module(body=[canon],type_ignores=[]),str(H),'exec'),env)
tail=[];active=False
for n in tr.body:
 if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='new' for t in n.targets):active=True
 if active and isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='path' for t in n.targets):break
 if active:tail.append(n)
exec(compile(ast.Module(body=tail,type_ignores=[]),str(H),'exec'),env)
a=env['new'];original=env['old'];inverse=copy.deepcopy(a);inverse.pop('root_exact_canonical_identity_copy')
fields=['candidate','candidate_promotions','candidate_builder','identity_sidecar','identity_integrity','original_source53_final_offer','final_independent_candidate_mapping_peer','actual_isolated_candidate_preparation','preserved_original_draft_offer','mapped_ledger','mapped_promotions','original_installed26_exact_byte_copies','original_closed_byte_aliases','required_evidence_artifacts_sha256','scope']
for k in fields:inverse[k]=copy.deepcopy(original[k])
assert inverse==original
assert a['mapped_ledger_sha256']==original['mapped_ledger_sha256'] and a['mapped_promotions_sha256']==original['mapped_promotions_sha256']
assert a['proof_files']=={} and a['new_actual_paired_records']==[] and a['new_material_keys']==[]
assert a['entire_original_independent_identity_peer_body_and_time']==env['peer'] and len(a['required_evidence_artifacts_sha256'])>=len(original['required_evidence_artifacts_sha256'])
assert all(not Path(n).is_absolute() for n in a['required_evidence_artifacts_sha256'])
fixtures=[]
def accept(label,v):
 got=env['canon'](v);assert got['sha256']==v['sha256'];fixtures.append({'name':label,'expected_accept':True,'observed_accept':True,'explicit_synthetic_input':True})
def reject(label,v):
 ok=False
 try:env['canon'](v);ok=True
 except (AssertionError,KeyError,FileNotFoundError):pass
 assert not ok;fixtures.append({'name':label,'expected_accept':False,'observed_accept':False,'explicit_synthetic_input':True})
for field in ['candidate','candidate_promotions','candidate_builder','final_independent_candidate_mapping_peer','actual_isolated_candidate_preparation']:
 accept('native original alias '+field,original[field]);bad=copy.deepcopy(original[field]);bad['sha256']='0'*64;reject('alias digest conflict '+field,bad)
accept('native unchanged Root evidence',{'file':next(iter(env['pack']['unchanged_root_evidence_sha256'])),'sha256':next(iter(env['pack']['unchanged_root_evidence_sha256'].values()))})
reject('unbound absent TMP reference',{'file':'/tmp/nonexistent-unapproved-copy-test27.json','sha256':'0'*64})
for n,h in env['held'].items():assert sha(R/n)==h
assert sha(R/'book/coverage/inventory.json')==env['INV_SHA'] and not env['BASE'].exists()
closed={str(H.relative_to(R)):sha(H),str(OLD.relative_to(R)):sha(OLD),str(Path(__file__)):sha(Path(__file__)),str(env['PACK']):sha(env['PACK'])}
for r in env['originals'].values():closed[r['file']]=r['sha256']
closed.update(env['pack']['unchanged_root_evidence_sha256'])
result={'status':'passed_independent_full_and_exact_delta_zero_proof_applied27_identity_copy2_code_native_prewrite_and_reversal_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':H.relative_to(R).as_posix(),'sha256':sha(H)},'helper_sha256':sha(H),'original_v1_draft':{'file':OLD.relative_to(R).as_posix(),'sha256':sha(OLD)},'exact_reverse_to_original_v1_except_native_raw_log_and_helper_workdir_guards':True,'actual_native_read_only_prewrite_passed':True,'pure_memory_offer_reverse_recovers_entire_original_b98f_body_and_time':True,'new_proof_sources':0,'original_peer_body_and_time_exact':True,'candidate_and_promotions_bytes_unchanged':True,'original_alias_count':len(env['pack']['original_closed_byte_aliases']),'unchanged_root_ref_count':len(env['pack']['unchanged_root_evidence_sha256']),'fixtures':fixtures,'closed_evidence_sha256':closed,'scope':'Independent code/read-only native prewrite plus exact whole-offer inverse in memory and12 explicit reference-routing fixtures. No Root copy helper execution, canonical copy, installed owner, compiler or aggregate claim.'}
with O.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','peer':str(O),'sha256':sha(O),'fixtures':len(fixtures)}))
