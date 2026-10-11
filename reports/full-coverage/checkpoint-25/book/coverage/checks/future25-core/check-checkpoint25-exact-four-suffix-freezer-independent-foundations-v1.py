from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased'); BASE=ROOT/'book/coverage/checks/future25-core'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
HELP='book/coverage/freeze_checkpoint25_v1.py'; OLD='book/coverage/freeze_checkpoint.py'; SEL='reports/full-coverage/checkpoint-25-selection.json'
assert H(ROOT/HELP)=='16044ad0d941f9a934237bd4bd244b8851213d5fe46bbb792cb4b7efd1c0775d'
assert H(ROOT/OLD)=='330453d4e8ad3952fe2a4f1f3b97c59dce9afbcbf0466162c5b414636d5b4017'
assert H(ROOT/SEL)=='3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff'
new=ast.parse((ROOT/HELP).read_text()); old=ast.parse((ROOT/OLD).read_text())
constants={n.targets[0].id:ast.literal_eval(n.value)for n in new.body if isinstance(n,ast.Assign)and isinstance(n.targets[0],ast.Name)and n.targets[0].id.startswith('CHECKPOINT25_')}
exc=constants['CHECKPOINT25_EXACT_EXTRA_SUFFIX_EXCEPTIONS']; assert len(exc)==4 and sum(Path(n).suffix=='.olean'for n in exc)==3 and sum(Path(n).suffix=='.yml'for n in exc)==1
selection=json.loads((ROOT/SEL).read_text()); assert len(selection['proof_files'])==1156
for n,h in exc.items():
 assert H(ROOT/n)==h and selection['extra_frozen_inputs'][n]['sha256']==h and selection['extra_frozen_inputs'][n]['scope']=='immutable_audit_or_local_source_evidence'
 assert n not in selection['proof_files'] and not n.startswith('verification/lean/')
# Remove only added constants/exact-selection guards and restore the one suffix clause.
restored=copy.deepcopy(new)
restored.body=[n for n in restored.body if not(isinstance(n,ast.Assign)and isinstance(n.targets[0],ast.Name)and n.targets[0].id.startswith('CHECKPOINT25_'))and not(isinstance(n,ast.If)and 'CHECKPOINT25_SELECTION' in ast.unparse(n))and not(isinstance(n,ast.For)and 'CHECKPOINT25_EXACT_EXTRA_SUFFIX_EXCEPTIONS.items()' in ast.unparse(n.iter))]
class Restore(ast.NodeTransformer):
 def visit_BoolOp(self,n):
  if isinstance(n.op,ast.And) and len(n.values)==2 and 'CHECKPOINT25_EXACT_EXTRA_SUFFIX_EXCEPTIONS.get(name)'in ast.unparse(n):return n.values[0]
  return self.generic_visit(n)
restored=Restore().visit(restored)
assert ast.dump(restored,include_attributes=False)==ast.dump(old,include_attributes=False),'unreviewed generic freezer code delta'
selection_gate=next(n for n in new.body if isinstance(n,ast.If)and 'CHECKPOINT25_SELECTION' in ast.unparse(n))
membership_gate=next(n for n in new.body if isinstance(n,ast.For)and 'CHECKPOINT25_EXACT_EXTRA_SUFFIX_EXCEPTIONS.items()' in ast.unparse(n.iter))
extra_loop=next(n for n in new.body if isinstance(n,ast.For)and "selection.get('extra_frozen_inputs'" in ast.unparse(n.iter))
# Actual producer guard ASTs, executed read-only against real paths or explicitly synthetic values.
checks=[]
def fixture(label,accept,sel=None,name=None,record=None,selarg=None,selhash=None,bytehash=None):
 s=copy.deepcopy(selection if sel is None else sel)
 env={'ROOT':ROOT,'Path':Path,'selection':s,'args':type('Args',(),{'selection':Path(SEL if selarg is None else selarg)})(),'selection_path':ROOT/SEL,'files':[],**constants}
 def sh(p):
  if Path(p)==ROOT/SEL and selhash is not None:return selhash
  if name is not None and Path(p)==ROOT/name and bytehash is not None:return bytehash
  return H(p)
 env['sha']=sh
 nodes=[selection_gate,membership_gate]
 if name is not None:
  env['selection']=copy.deepcopy(s); env['selection']['extra_frozen_inputs']={name:copy.deepcopy(record)}; nodes=[extra_loop]
 try:exec(compile(ast.fix_missing_locations(ast.Module(body=copy.deepcopy(nodes),type_ignores=[])),HELP,'exec'),env); ok=True
 except (ValueError,KeyError,FileNotFoundError):ok=False
 assert ok==accept,(label,ok,accept)
 checks.append({'name':label,'accepted':ok,'expected_acceptance':accept,'kind':'isolated read-only actual guard-AST fixture; no freeze execution'})
fixture('exact actual selection and all four memberships',True)
fixture('wrong selection path',False,selarg='reports/full-coverage/checkpoint-24-selection.json')
fixture('wrong selection bytes',False,selhash='0'*64)
for i,(n,h)in enumerate(exc.items()):
 r=selection['extra_frozen_inputs'][n]
 fixture('actual archive '+str(i),True,name=n,record=r)
 s=copy.deepcopy(selection);del s['extra_frozen_inputs'][n];fixture('missing required exception '+str(i),False,sel=s)
 s=copy.deepcopy(selection);s['extra_frozen_inputs'][n]['sha256']='0'*64;fixture('changed membership digest '+str(i),False,sel=s)
 rr=copy.deepcopy(r);rr['scope']='selected_proof';fixture('wrong archive scope '+str(i),False,name=n,record=rr)
 fixture('changed archive bytes '+str(i),False,name=n,record=r,bytehash='0'*64)
 fixture('other archive name with exact allowed digest '+str(i),False,name=n+'.other'+Path(n).suffix,record=r,bytehash=h)
 fixture('absolute archive path '+str(i),False,name=str(ROOT/n),record=r,bytehash=h)
 fixture('traversal archive path '+str(i),False,name='book/coverage/../coverage/'+n.removeprefix('book/coverage/'),record=r,bytehash=h)
 fixture('noncanonical archive path '+str(i),False,name='./'+n,record=r,bytehash=h)
 fixture('outside provenance root '+str(i),False,name='verification/lean/'+Path(n).name,record=r,bytehash=h)
regular=next((n,r)for n,r in selection['extra_frozen_inputs'].items()if Path(n).suffix in {'.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt'}and n not in exc)
fixture('unchanged generic allowed suffix',True,name=regular[0],record=regular[1])
for suffix in ['.olean','.yml','.yaml','.bin','.so']:
 fixture('unauthorized suffix '+suffix,False,name='book/coverage/checks/unauthorized-freezer-fixture'+suffix,record={'scope':'immutable_audit_or_local_source_evidence','sha256':'a'*64},bytehash='a'*64)
assert all(Path(n).suffix=='.lean' and n.startswith('verification/lean/SafeLearning/')for n in selection['proof_files'])
assert all(not any(n==x for x in exc)for n in selection['proof_files'])
# Stable public identity inputs, not a redundant full historical snapshot audit.
inv=ROOT/'book/coverage/inventory.json';assert H(inv)=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
protected={str(p.relative_to(ROOT)):H(p)for p in (ROOT/'SafeLearning').iterdir()if p.suffix in {'.html','.css','.js'}}
assert len(protected)==31
for o in ['core','foundations','applied','modules','applied-promotions']:protected['book/coverage/'+o+'.json']=H(ROOT/'book/coverage'/ (o+'.json'))
obs={'status':'independent_exact_four_archival_suffix_freezer_code_and_fixture_review_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; helper author Modules','helper':{'file':HELP,'sha256':H(ROOT/HELP)},'helper_sha256':H(ROOT/HELP),'original_generic_helper':{'file':OLD,'sha256':H(ROOT/OLD)},'selection':{'file':SEL,'sha256':H(ROOT/SEL)},'exceptions':exc,'full_generic_AST_restored_exact_after_only_reviewed_delta':True,'archive_files_checked_byte_exact':4,'exception_files_selected_as_proof_sources':0,'selected_source_count':1156,'fixtures':checks,'fixture_count':len(checks),'current_inventory_sha256':H(inv),'protected_current_sha256':protected,'scope':'Code review and actual read-only producer guard fixtures only. No freezer/snapshot/Lean/kernel/publication execution; three olean archives are historical compiler bytes, not proof imports. Actual production freeze retains all original proof/evidence/scope/path/root/hash guards.'}
for n,h in protected.items():assert H(ROOT/n)==h
OUT=BASE/'checkpoint25-exact-four-extra-suffix-freezer-independent-foundations-observation-v1.json';assert not OUT.exists();OUT.write_text(json.dumps(obs,indent=2)+'\n');print(json.dumps({'status':obs['status'],'fixture_count':len(checks),'observation':str(OUT.relative_to(ROOT))}))
