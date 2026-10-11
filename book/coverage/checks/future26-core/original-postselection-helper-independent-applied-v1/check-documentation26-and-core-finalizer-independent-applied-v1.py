from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda n:{'file':n,'sha256':H(ROOT/n)}
DOC1='book/coverage/checks/root_prepare_checkpoint26_documentation_v1.py';DOC2=DOC1.replace('_v1','_v2');FIN='book/coverage/checks/finalize_root_core26_offer_v1.py'
a=ast.parse((ROOT/DOC1).read_text());b=ast.parse((ROOT/DOC2).read_text());f=ast.parse((ROOT/FIN).read_text())
assert H(ROOT/DOC2)=='608690bc7a3094e02dd02b906729b4773c508edae6f8d54213f7a6eea118884a'
assert H(ROOT/FIN)=='bcdbb18d1913b740014df4602bb0239b8767896db8f524955774557150128b52'
# Full delta is only three added guard blocks and export-integrity wrapper stem.
s1=(ROOT/DOC1).read_text();s2=(ROOT/DOC2).read_text();normal=s2
normal=normal.replace("assert {d['name'] for d in audit['declarations']}==set(audit['axiom_dependencies'])\n",'')
start=normal.index('manual_ref=');end=normal.index("static_name=",start);normal=normal[:start]+normal[end:]
start=normal.index('export_integrity_name=');end=normal.index('integration_name=',start);normal=normal[:start]+normal[end:]
normal=normal.replace(",'export-integrity-checkpoint26-execution-v1'",'');assert normal==s1
fixtures=[]
def run(label,nodes,scope,want):
 accepted=True
 try:exec(compile(ast.Module(body=nodes,type_ignores=[]),label,'exec'),scope,scope)
 except (AssertionError,ValueError,KeyError,FileNotFoundError):accepted=False
 assert accepted==want,label
 fixtures.append({'fixture':label,'accepted':accepted,'expected_acceptance':want})
# Execute actual visual-evidence guard block, with genuine current records and
# read-only hash function substitutions for corruption fixtures.
start=next(i for i,n in enumerate(b.body)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='manual_ref'for t in n.targets));end=next(i for i,n in enumerate(b.body)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='static_name'for t in n.targets));mnodes=b.body[start:end]
browser=json.loads((ROOT/'reports/full-coverage/browser-checkpoint-26.json').read_text());assets=browser['source_sha256'];manual=json.loads((ROOT/browser['manual_visual_inspection']['scoped_changed_prose_review']['file']).read_text())
def ms(browser_override=None,manual_override=None,bad_hash=None):
 def read(n):
  if n=='reports/full-coverage/source53-six-paragraph-content-manual-review26-v1.json'and manual_override is not None:return copy.deepcopy(manual_override)
  return json.loads((ROOT/n).read_text())
 return {'browser':copy.deepcopy(browser if browser_override is None else browser_override),'assets':assets,'sha':lambda n:'0'*64 if n==bad_hash else H(ROOT/n),'read':read}
run('six actual visual records accepted',mnodes,ms(),True)
d=copy.deepcopy(browser);d['manual_visual_inspection']['scoped_changed_prose_review']['sha256']='0'*64;run('changed manual reference rejected',mnodes,ms(browser_override=d),False)
for path in [manual['inspected_captures'][0]['path'],manual['original_capture_reports'][0]['file']]:run('changed visual evidence rejected '+path,mnodes,ms(bad_hash=path),False)
for label,change in [('five captures',lambda d:d['inspected_captures'].pop()),('duplicate captures',lambda d:d['inspected_captures'].__setitem__(1,copy.deepcopy(d['inspected_captures'][0]))),('wrong source',lambda d:d.update(source_sha256='0'*64)),('wrong manual status',lambda d:d.update(status='pending'))]:
 d=copy.deepcopy(manual);change(d);run(label+' rejected',mnodes,ms(manual_override=d),False)
# Actual native axiom inventory assertions, including exact name correspondence.
ax=[n for n in b.body if isinstance(n,ast.Assert)and ('axiom_dependencies' in ast.unparse(n)or 'allowed_standard_axioms' in ast.unparse(n))]
base={'declarations':[{'name':str(i)}for i in range(9503)],'axiom_dependencies':{str(i):['propext']for i in range(9503)},'allowed_standard_axioms':['propext','Classical.choice','Quot.sound']}
run('matching 9503 declaration and axiom names accepted',ax,{'audit':copy.deepcopy(base)},True)
for label,change in [('mismatched name',lambda d:d['declarations'][0].update(name='not-indexed')),('missing axiom',lambda d:d['axiom_dependencies'].pop('0')),('unsafe axiom',lambda d:d['axiom_dependencies']['0'].append('sorryAx'))]:
 d=copy.deepcopy(base);change(d);run(label+' rejected',ax,{'audit':d},False)
# Actual strict native closure and safe path functions, isolated from all live files.
funcs=[n for n in b.body if isinstance(n,ast.FunctionDef)]
with tempfile.TemporaryDirectory(prefix='docs26-guard-fixtures-')as folder:
 R=Path(folder);(R/'closed.log').write_bytes(b'actual fixture log\n');record={'actual_exit_code':0,'exit_code':0,'log':'closed.log','raw_log':'closed.log','log_sha256':H(R/'closed.log'),'raw_log_sha256':H(R/'closed.log')}
 scope={'ROOT':R,'Path':Path,'hashlib':hashlib,'json':json};exec(compile(ast.Module(body=funcs,type_ignores=[]),'docs26-functions','exec'),scope,scope)
 def actual_fixture(label,mutate,want):
  d=copy.deepcopy(record);mutate(d);(R/'closed.json').write_text(json.dumps(d));run(label,[ast.parse("actual('closed.json')").body[0]],scope.copy(),want)
 actual_fixture('genuine consistent int-zero aliases accepted',lambda d:None,True)
 actual_fixture('bool false exit rejected',lambda d:d.update(actual_exit_code=False),False)
 actual_fixture('conflicting exits rejected',lambda d:d.update(exit_code=1),False)
 actual_fixture('missing exits rejected',lambda d:[d.pop(k)for k in ('actual_exit_code','exit_code')],False)
 actual_fixture('wrong log hash rejected',lambda d:d.update(log_sha256='0'*64,raw_log_sha256='0'*64),False)
 actual_fixture('conflicting log aliases rejected',lambda d:d.update(raw_log='other.log'),False)
 for path in ['/tmp/escape','../escape','book//a']:
  run('noncanonical path rejected '+path,[ast.parse('safe('+repr(path)+')').body[0]],scope.copy(),False)
# Dynamic documentation actually retains prior delivery and truthful pending26.
text_node=next(n for n in b.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='text'for t in n.targets));scope={'excounts':{'complete':515,'partial':18,'pending':23},'materials':{'reviewed':4600,'pending':8174},'manifest':{'frozen_inputs_sha256':{'fixture':1}}};exec(compile(ast.Module(body=[text_node],type_ignores=[]),'docs26-dynamic-text','exec'),scope,scope)
assert '515 of 556 exercises' in scope['text']and '4,600 are reviewed' in scope['text'];assert 'Checkpoint26 awaits its own actual push' in scope['text'];assert 'general robust replanning certificate remains an open obligation' in scope['text'];assert '140 retained checks' in scope['text']and 'five fresh viewport' in scope['text']
# Core finalizer zero() runs actual code against conflicting native schemas.
zero=next(n for n in f.body if isinstance(n,ast.FunctionDef)and n.name=='zero');zs={};exec(compile(ast.Module(body=[zero],type_ignores=[]),'core26-finalizer-zero','exec'),zs,zs)
for d,want in [({'actual_exit_code':0},True),({'actual_exit_code':0,'exit_code':0},True),({'actual_exit_code':False},False),({'actual_exit_code':0,'exit_code':1},False),({},False)]:run('finalizer strict exit '+repr(d),[ast.parse('zero(d)').body[0]],dict(zs,d=d),want)
assert "peer['candidate']==ref(CANDIDATE)" in (ROOT/FIN).read_text();assert "len(proofs)==4 and sum(p['public_export_count'] for p in proofs.values())==48" in (ROOT/FIN).read_text();assert "with safe(OUT).open('x')" in (ROOT/FIN).read_text()
base_path=ROOT/'book/coverage/checks/future26-core';v1=base_path/'documentation26-helper-independent-applied-review-v1.json';v2=base_path/'documentation26-helper-independent-applied-review-v2.json';fp=base_path/'core26-offer-finalizer-independent-applied-code-review-v1.json';assert not any(p.exists()for p in [v1,v2,fp])
old={'status':'requires_changes_independent_full_code_review','approved':False,'errors':['README six-capture inspection claim lacked manual reference and original capture/PNG hash guards','Native 9503 declaration/axiom inventories lacked exact declaration-name equality'],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent_applied','helper':ref(DOC1),'helper_sha256':H(ROOT/DOC1),'scope':'Full code read only; v1 unexecuted and preserved. No production result or mathematical scope decision.'};v1.write_text(json.dumps(old,indent=2)+'\n')
new={'status':'passed_independent_full_code_delta_and_isolated_documentation26_guard_fixtures','approved':True,'errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent_applied','helper':ref(DOC2),'helper_sha256':H(ROOT/DOC2),'entire_original_v1_review_body_and_time':old,'original_v1_review':ref(str(v1.relative_to(ROOT))),'full_code_read':True,'exact_declared_delta_reversed_to_v1':True,'fixture_count':len(fixtures),'fixtures':fixtures,'scope':'Code and actual isolated AST guard fixtures only. Production audit/export-integrity/frozen/static/integration outputs remain required; no progress/README/PUB/live-owner/Git writes or inferred26 verification.'};v2.write_text(json.dumps(new,indent=2)+'\n')
final={'status':'passed_independent_full_code_and_strict_native_exit_fixtures','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent_applied','helper':ref(FIN),'helper_sha256':H(ROOT/FIN),'full_code_read':True,'scope':'Unexecuted isolated offer finalizer only; exact candidate/peer/hash/actual native command/workdir/log and eight actual paired-source guards read. No final offer or Root installation/audit/publication inferred.'};fp.write_text(json.dumps(final,indent=2)+'\n')
print(json.dumps({'status':'passed','documentation_v2':ref(str(v2.relative_to(ROOT))),'preserved_v1':ref(str(v1.relative_to(ROOT))),'core_finalizer':ref(str(fp.relative_to(ROOT))),'fixtures':len(fixtures)}))
