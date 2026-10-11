from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,importlib.util,sys,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=Path('/tmp/modules-zero-sign-source58-independent-foundations-parser28-v2');OUT=Path('/tmp/modules-zero-sign-source58-independent-foundations-parser28-findings-v2.json');REQ=Path('/tmp/modules-ibp-zero-sign-source58-proposal28-v1/modules-ibp-zero-sign-source58-proposal28-v1.json')
assert not BASE.exists()and not OUT.exists();BASE.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
def read(p):return json.loads(Path(p).read_text())
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute()else ROOT/p
 assert p.is_file()and sha(p)==r['sha256'];return p
assert sha(REQ)=='7505b1d64cb9b3a55be0001ac7dff8379f3bc35b15606a41fb010c20ead4cc3b';j=read(REQ)
sel=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json');assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256'];owners={r['destination']:r['candidate']['sha256']for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']};held={n:r['sha256']for n,r in sel['proof_files'].items()};held.update(assets);held.update(owners);held['book/coverage/inventory.json']='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf';held['book/coverage/material-corrections.json']='21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'
def guard():
 for n,h in held.items():assert sha(ROOT/n)==h,n
started=datetime.now(timezone.utc).isoformat();guard();inv=read(checked(j['before_inventory']));original=checked(j['source']).read_bytes();candidate=checked(j['proposed_source']).read_bytes();a=j['before_raw_fragment'].encode();b=j['after_raw_fragment'].encode();assert original.count(a)==candidate.count(b)==1 and original.replace(a,b)==candidate and candidate.replace(b,a)==original
assert j['full_current_context_lines120_to130']==''.join(original.decode().splitlines(keepends=True)[119:130]);assert j['full_proposed_context_lines120_to130']==''.join(candidate.decode().splitlines(keepends=True)[119:130])
assert 'which is feasible in the box (with $\\mathrm{sign}(0)=0$)'in j['after_raw_fragment'];assert'either endpoint'in j['after_raw_fragment'];assert'zero-weight entry'in j['after_raw_fragment']
(BASE/'SafeLearning').mkdir()
for p in sorted((ROOT/'SafeLearning').glob('*.html')):shutil.copyfile(p,BASE/'SafeLearning'/p.name)
assert len(list((BASE/'SafeLearning').glob('*.html')))==29;(BASE/'SafeLearning/verification.html').write_bytes(candidate)
sys.path.insert(0,str(ROOT/'book'));spec=importlib.util.spec_from_file_location('isolated_inventory_zero_sign58',checked(j['parser']));module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);module.ROOT=BASE;module.OUT=BASE/'book/coverage';assert module.ROOT!=ROOT and module.OUT!=ROOT/'book/coverage';module.inventory();fresh=read(module.OUT/'inventory.json');expected=read(checked(j['proposed_full29_inventory']));assert{k:v for k,v in fresh.items()if k!='generated_at_utc'}=={k:v for k,v in expected.items()if k!='generated_at_utc'}
changes={}
for family in('exercises','material_source_units'):
 old={r['key']:r for r in inv[family]};new={r['key']:r for r in fresh[family]};assert old.keys()==new.keys();changes[family]=sorted(k for k in old if old[k]['source_text']!=new[k]['source_text'])
 for k in old:
  left,right=dict(old[k]),dict(new[k]);left.pop('source_sha256');right.pop('source_sha256')
  if k!='verification.html::node-193':assert left==right,k
assert changes==j['fresh_parser_changed_text_keys']=={'exercises':[],'material_source_units':['verification.html::node-193']};assert fresh['counts']==inv['counts']and len(fresh['source_sha256'])==29
for n,h in fresh['source_sha256'].items():assert h==(sha(checked(j['proposed_source']))if n=='SafeLearning/verification.html'else inv['source_sha256'][n])
guard();closed={str(REQ):sha(REQ)}
for k in('before_inventory','source','parser','proposed_source','proposed_full29_inventory','current_modules_owner'):p=checked(j[k]);closed[str(p)]=sha(p)
d={'status':'passed_independent_source58_zero_sign_wording_and_isolated_full29_parser','reviewer':'/root/foundations_recovery28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'started_at_utc':started,'errors':[],'proposal':ref(REQ),'fresh_parser_inventory':ref(module.OUT/'inventory.json'),'fresh_parser_literal_changes':changes,'counts':fresh['counts'],'both_parser_ROOT_and_OUT_isolated':True,'full_current_and_proposed_context120_130_read':True,'exact_forward_and_inverse_whole_source_passed':True,'semantic_decision':'The standard-sign witness is feasible and attains the row bound; a zero-weight coordinate with positive radius is centered, not an endpoint. Replacing only zero-weight coordinates by either endpoint yields a corner and leaves every zero-weight contribution zero. The corrected wording is faithful for the stated nonnegative box radii, including degenerate radii.','approved_narrow_wording':True,'whole_material_or_exercise_approved':False,'compiler_or_kernel_execution_claimed':False,'canonical_source_write_claimed':False,'current_selected_source_count':1175,'current_asset_count':31,'current_owner_count':5,'held_sha256_before_and_after':held,'closed_evidence_sha256':closed,'scope':'Independent narrow-source semantic/full29 isolated-parser peer. Formal affine/exercise full-scope review remains Applied responsibility and no source58 application occurs.'}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'changes':changes,'counts':fresh['counts']}))
