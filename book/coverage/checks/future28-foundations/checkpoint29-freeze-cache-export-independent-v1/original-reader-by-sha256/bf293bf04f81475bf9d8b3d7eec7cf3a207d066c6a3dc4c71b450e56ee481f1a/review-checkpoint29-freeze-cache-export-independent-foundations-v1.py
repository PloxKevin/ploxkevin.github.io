from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,difflib
R=Path('/home/oxrexkevin/SafetyBased');C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
pins={'book/coverage/freeze_checkpoint29_v1.py':'3ac0b8f09c445b84de1e5bb429072ea27f1a0b13e0ce59400c229cac900b9694','book/coverage/checks/root_prepare_checkpoint29_cache_v1.py':'82e2f34e962fb94bee8080be71ac26d5c336a30c7e6ef6fdbd35a4d2650b0693','book/coverage/export_audit29_v1.py':'9f98adda1cca5899f431e3c7c1bb2519f0e00b7be24a3f23d23308349ad1fed3','book/coverage/freeze_checkpoint28_v1.py':'545d20ddc9cb15c35f93297da01c6f7ecdfc9ab64b8eb351f379e580698e3607','book/coverage/checks/root_prepare_checkpoint28_cache_v1.py':'df43626d818b31d3ae1eedd14064184a8a498f1bdd6089f6b31b71dbe62586e6','book/coverage/export_audit28_v1.py':'9402d0c0d89ed910c783a1a406fcaea90f751371e3edbe30fda8caca2c05b9e1'}
def sha(n):return hashlib.sha256((Path(n) if Path(n).is_absolute() else R/n).read_bytes()).hexdigest()
ctx=json.loads(C.read_bytes());start=datetime.now(timezone.utc).isoformat()
def guard():
 for n,h in pins.items():assert sha(n)==h,n
 for k in ('pins_sha256','held_current_source_sha256','owners_sha256'):
  for n,h in ctx[k].items():assert sha(n)==h,n
guard();diffs={}
for new,old in [('book/coverage/freeze_checkpoint29_v1.py','book/coverage/freeze_checkpoint28_v1.py'),('book/coverage/checks/root_prepare_checkpoint29_cache_v1.py','book/coverage/checks/root_prepare_checkpoint28_cache_v1.py'),('book/coverage/export_audit29_v1.py','book/coverage/export_audit28_v1.py')]:
 a=(R/old).read_text();b=(R/new).read_text();ast.parse(a);ast.parse(b)
 diffs[new]=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile=old,tofile=new))
 if 'freeze_checkpoint' in new:
  expected=a.replace('CHECKPOINT28','CHECKPOINT29').replace('checkpoint-28','checkpoint-29').replace('checkpoint28','checkpoint29').replace('== 1186','== 1197').replace("'.lean', '.js'}","'.lean', '.js', '.mjs'}").replace("'.lean', '.js', '.cjs'","'.lean', '.js', '.mjs', '.cjs'")
 elif 'prepare_checkpoint' in new:
  expected=a.replace('checkpoint-28','PHASE29').replace('checkpoint-27','checkpoint-28').replace('PHASE29','checkpoint-29').replace('==1186 and','==1197 and').replace('original27','original28').replace('==1175','==1186').replace('checkpoint28-cache','checkpoint29-cache')
 else:expected=a.replace('checkpoint-28','checkpoint-29').replace('== 1186','== 1197').replace('== 9896','== 10114')
 assert b==expected,new
selection=json.loads((R/'reports/full-coverage/checkpoint-28-selection.json').read_bytes());assert len(selection['proof_files'])==1186
audit=json.loads((R/'reports/full-coverage/lean-checkpoint-28/verification-original.json').read_bytes());assert audit['proof_file_count']==1186 and audit['theorem_count']==9896 and audit['status']=='passed'
assert all(type(c['exit_code']) is int and c['exit_code']==0 for c in audit['checks'])
assert audit['proof_sha256']=={n:q['sha256'] for n,q in selection['proof_files'].items()}
assert 1186+11==1197 and 9896+218==10114
js=[]
for n in (R/'book/coverage').rglob('*.mjs'):
 if n.is_file() and '__pycache__' not in n.parts:js.append({'file':n.relative_to(R).as_posix(),'sha256':sha(str(n))})
guard()
out={'status':'passed_independent_full_checkpoint29_freeze_cache_export_code_delta_review_foundations','errors':[],'started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewed_helpers_sha256':pins,'exact_full_old28_to_new29_deltas':diffs,'current65_context':{'file':str(C),'sha256':sha(str(C))},'baseline28_selection':{'file':'reports/full-coverage/checkpoint-28-selection.json','sha256':sha('reports/full-coverage/checkpoint-28-selection.json')},'baseline28_original_audit':{'file':'reports/full-coverage/lean-checkpoint-28/verification-original.json','sha256':sha('reports/full-coverage/lean-checkpoint-28/verification-original.json')},'expected_checkpoint29_source_theorem_counts':[1197,10114],'mjs_prospective_evidence_inputs':js,'full_code_delta_findings':[],'inherited_export_gate_scope':'Exporter checks report status and primary exact integer exit_code. It relies on genuine frozen verifier output and the surrounding actual command/helper/provenance gates; it does not independently enforce every optional native alias. Original execution commands/times/historical original_check paths stay unchanged.','future_real29_selection_freeze_build_kernel_axiom_export_and_ledger_check_required':True,'actual29_freeze_cache_build_export_or_verification_executed':False,'no_import_or_top_level_execution_of_any_production_helper':True,'protection_errors':[],'coverage_complete':False}
Path('/tmp/checkpoint29-freeze-cache-export-independent-foundations-findings-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'full_code_delta_findings':[],'current_proof_sources':1186,'future_expected_source_theorem_counts':[1197,10114],'production_executed':False}))
