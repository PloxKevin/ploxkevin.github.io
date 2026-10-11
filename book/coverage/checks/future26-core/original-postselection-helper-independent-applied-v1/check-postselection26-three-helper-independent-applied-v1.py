from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,tempfile,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda n:{'file':n,'sha256':H(ROOT/n)}
FREEZE='book/coverage/freeze_checkpoint26_v1.py';CACHE='book/coverage/checks/root_prepare_checkpoint26_cache_v1.py';EXPORT='book/coverage/checks/root_check_export26_integrity_v3.py'
helpers={n:(ROOT/n).read_text()for n in [FREEZE,CACHE,EXPORT]}
for n,s in helpers.items():ast.parse(s)
assert H(ROOT/FREEZE)=='c166cdbb81d19d47aa629b658e944250dab2cf401b2aa4f9d4956d3852ce2e6e'
ft=ast.parse(helpers[FREEZE]);exnode=next(n for n in ft.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='CHECKPOINT26_EXACT_EXTRA_SUFFIX_EXCEPTIONS'for t in n.targets));exceptions=ast.literal_eval(exnode.value);assert len(exceptions)==6
for n,h in exceptions.items():assert H(ROOT/n)==h
extra=next(n for n in ft.body if isinstance(n,ast.For)and ast.unparse(n.target)=='(name, record)'and 'extra_frozen_inputs' in ast.unparse(n.iter))
extra_code=compile(ast.Module(body=[extra],type_ignores=[]),FREEZE+'-exact-extra-input-guard-fixture','exec')
# Actual guard AST is run against isolated byte-exact copies only. Production
# selection/snapshot creation and all working inputs remain untouched.
fixtures=[]
with tempfile.TemporaryDirectory(prefix='postselection26-independent-')as folder:
 R=Path(folder)
 for n in exceptions:
  p=R/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((ROOT/n).read_bytes())
 p=R/'book/coverage/synthetic-reviewed.cjs';p.write_text('module.exports = 1;\n')
 def guard(rows):
  scope={'ROOT':R,'Path':Path,'sha':lambda p:H(p),'selection':{'extra_frozen_inputs':rows},'CHECKPOINT26_EXACT_EXTRA_SUFFIX_EXCEPTIONS':exceptions,'files':[]}
  exec(extra_code,scope,scope);return scope['files']
 def fixture(label,rows,accepted):
  okay=True
  try:guard(rows)
  except (AssertionError,ValueError,KeyError,FileNotFoundError):okay=False
  assert okay==accepted,label;fixtures.append({'fixture':label,'accepted':okay,'expected_acceptance':accepted})
 valid={n:{'sha256':h,'scope':'immutable_audit_or_local_source_evidence'}for n,h in exceptions.items()}
 fixture('six exact archival originals accepted',valid,True)
 fixture('ordinary reviewed cjs accepted',{'book/coverage/synthetic-reviewed.cjs':{'sha256':H(p),'scope':'immutable_audit_or_local_source_evidence'}},True)
 for n in exceptions:
  wrong=copy.deepcopy(valid);wrong[n]['sha256']='0'*64;fixture('wrong digest rejected '+n,wrong,False)
 n=next(iter(exceptions));wrong=copy.deepcopy(valid);wrong[n]['scope']='selected_proof_source';fixture('archive promoted into proof scope rejected',wrong,False)
 for suffix in ['.olean','.yml','.png']:
  p=R/('book/coverage/undeclared'+suffix);p.write_bytes(b'fixture')
  fixture('undeclared '+suffix+' rejected',{str(p.relative_to(R)):{'sha256':H(p),'scope':'immutable_audit_or_local_source_evidence'}},False)
 for n in ['/tmp/outside.olean','book/coverage/../coverage/undeclared.olean','book/coverage//undeclared.olean','verification/lean/SafeLearning/Fake.olean']:
  fixture('escaping/noncanonical provenance path rejected '+n,{n:{'sha256':'0'*64,'scope':'immutable_audit_or_local_source_evidence'}},False)
 # Selection's mandatory six exceptions are a separate actual AST gate.
 mandatory=next(n for n in ft.body if isinstance(n,ast.For)and ast.unparse(n.target)=='(name, digest)'and 'CHECKPOINT26_EXACT_EXTRA_SUFFIX_EXCEPTIONS' in ast.unparse(n.iter))
 mcode=compile(ast.Module(body=[mandatory],type_ignores=[]),FREEZE+'-required-six-exceptions-fixture','exec')
 for label,rows,pass_expected in [('complete mandatory set',valid,True),('missing one mandatory archive',{k:v for k,v in valid.items()if k!=n},False)]:
  # Missing fixture uses the first real key, not the previous path loop value.
  if label.startswith('missing'):rows={k:v for k,v in valid.items()if k!=next(iter(valid))}
  okay=True
  try:exec(mcode,{'selection':{'extra_frozen_inputs':rows},'CHECKPOINT26_EXACT_EXTRA_SUFFIX_EXCEPTIONS':exceptions})
  except ValueError:okay=False
  assert okay==pass_expected;fixtures.append({'fixture':label,'accepted':okay,'expected_acceptance':pass_expected})
# Cache is identical to parent25 after only explicit checkpoint/count changes.
parent=(ROOT/'book/coverage/checks/root_prepare_checkpoint25_cache_v1.py').read_text()
expected=parent.replace('checkpoint-25','checkpoint-X').replace('checkpoint-24','checkpoint-25').replace('checkpoint-X','checkpoint-26').replace('checkpoint25-cache','checkpoint26-cache').replace('original24','original25').replace('==1156','==1167').replace('==12','==11').replace('==1144','==1156')
assert helpers[CACHE]==expected
assert "requires_real_build_and_kernel_audit"in helpers[CACHE]and "No compiler, kernel or axiom success inferred"in helpers[CACHE]
# Native export gates must reject missing/incorrect/unsafe axiom inventories.
et=ast.parse(helpers[EXPORT]);asserts=[n for n in et.body if isinstance(n,ast.Assert)]
axiom_asserts=[n for n in asserts if 'axiom_dependencies' in ast.unparse(n)]
assert any('len('in ast.unparse(n)and '9503'in ast.unparse(n)for n in axiom_asserts)
acode=compile(ast.Module(body=axiom_asserts,type_ignores=[]),EXPORT+'-axiom-guard-fixture','exec')
base={'theorem_count':9503,'declarations':[{'name':'theorem'+str(i)}for i in range(9503)],'axiom_dependencies':{'theorem'+str(i):['propext']for i in range(9503)},'allowed_standard_axioms':['propext','Classical.choice','Quot.sound']}
for label,mutate,okay_expected in [('full9503',lambda d:None,True),('empty dependency map',lambda d:d.update(axiom_dependencies={}),False),('one missing dependency',lambda d:d['axiom_dependencies'].pop('theorem0'),False),('wrong declaration names',lambda d:d['declarations'][0].update(name='unknown'),False),('duplicate declaration names',lambda d:d['declarations'][0].update(name='theorem1'),False),('unapproved axiom',lambda d:d['axiom_dependencies']['theorem0'].append('sorryAx'),False)]:
 d=copy.deepcopy(base);mutate(d);okay=True
 try:exec(acode,{'original':d})
 except AssertionError:okay=False
 assert okay==okay_expected;fixtures.append({'fixture':label,'accepted':okay,'expected_acceptance':okay_expected})
# Strict int-zero native exit aliases reject bool False, missing and nonzero.
exit_assert=next(n for n in asserts if 'type(c[' in ast.unparse(n));zcode=compile(ast.Module(body=[exit_assert],type_ignores=[]),EXPORT+'-native-exit-guard-fixture','exec')
for value in [0,False,1,None]:
 okay=True
 try:exec(zcode,{'original':{'checks':[{'exit_code':value}]}})
 except AssertionError:okay=False
 assert okay==(type(value)is int and value==0);fixtures.append({'fixture':'native exit '+repr(value),'accepted':okay,'expected_acceptance':type(value)is int and value==0})
report={'status':'passed_independent_code_delta_and_isolated_negative_fixtures_for_three_unexecuted_postselection26_helpers','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent_applied','helpers':{n:ref(n)for n in helpers},'full_code_read':True,'fixture_count':len(fixtures),'fixtures':fixtures,'six_exact_archival_suffix_exceptions':exceptions,'parent25_helpers_preserved_sha256':{n:H(ROOT/n)for n in ['book/coverage/freeze_checkpoint25_v1.py','book/coverage/checks/root_prepare_checkpoint25_cache_v1.py','book/coverage/checks/root_check_export25_integrity_v1.py']},'unexecuted_export26_v1_guard_omission_preserved':ref('book/coverage/checks/root_check_export26_integrity_v1.py'),'unexecuted_export26_v2_schema_draft_preserved':ref('book/coverage/checks/root_check_export26_integrity_v2.py'),'scope':'Code/delta and actual isolated AST guard fixtures only. No production selection, freeze, cache copy, compiler/kernel/axiom run, export or owner/PUB/Git execution. Exact selection SHA remains an independently reviewed future actual CLI input; all real26 outputs remain required.'}
p=ROOT/'book/coverage/checks/future26-core/postselection26-three-helpers-independent-applied-code-and-fixture-review-v1.json';assert not p.exists();p.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':'passed','report':ref(str(p.relative_to(ROOT))),'fixtures':len(fixtures)}))
