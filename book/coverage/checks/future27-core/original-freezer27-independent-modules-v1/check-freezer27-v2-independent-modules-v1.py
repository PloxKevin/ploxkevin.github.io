from pathlib import Path
from datetime import datetime,timezone
from types import SimpleNamespace
import ast,copy,hashlib,json,re,tempfile
R=Path('/home/oxrexkevin/SafetyBased');H=R/'book/coverage/freeze_checkpoint27_v2.py';V1=R/'book/coverage/freeze_checkpoint27_v1.py';OLD=R/'book/coverage/freeze_checkpoint26_v1.py';OUT=Path('/tmp/checkpoint27-freezer2-independent-modules-check-result-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p)}
assert sha(H)=='4c964b933eac26217b6965efb9b5f4e27649402f63b0a77662de0b5692af0e14' and sha(V1)=='9389d5d5c84181eb8de5dc242ffa49269dddd2626ed4268b6d74cd79429e6d25' and sha(OLD)=='c166cdbb81d19d47aa629b658e944250dab2cf401b2aa4f9d4956d3852ce2e6e'
s=H.read_text();v1=V1.read_text();old=OLD.read_text();assert s.replace("CHECKPOINT27_SELECTION = 'reports/full-coverage/checkpoint-27-selection.json'", "CHECKPOINT27_SELECTION = 'reports/full-coverage/checkpoint-26-selection.json'")==v1
tr=ast.parse(s);oldtr=ast.parse(old)
def literal(t,name):return ast.literal_eval(next(n.value for n in t.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id==name for x in n.targets)))
extra=literal(tr,'CHECKPOINT27_EXACT_EXTRA_SUFFIX_EXCEPTIONS');older=literal(oldtr,'CHECKPOINT26_EXACT_EXTRA_SUFFIX_EXCEPTIONS');newpath='book/coverage/checks/future27-core/closed-checkpoint26-delivery-originals-v2/original-root/reports/full-coverage/pages26-config-previous-original-v1.yml';newhash='7cbf6c4a7aa5c2f349b83025018e6a27898e567e1822f3aeab4d064fbfecb0af'
assert len(older)==6 and extra==older|{newpath:newhash}
normalized=s.replace('CHECKPOINT27','CHECKPOINT26').replace('checkpoint-27-selection.json','checkpoint-26-selection.json').replace('checkpoint27 selection','checkpoint26 selection').replace('only seven already selected','only six already selected').replace(" == 1175", " == 1167").replace("assert selection['new_file_count'] == 8", "assert selection['new_file_count'] == 11").replace(', '+repr(newpath)+': '+repr(newhash),'')
prune_lines="    expected_excluded = {'foundations': [], 'core': [], 'modules': [], 'applied': ['verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean', 'verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean', 'verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean']}\n    if excluded_metadata[domain] != expected_excluded[domain]:\n        raise ValueError('Unexpected excluded metadata: ' + domain)\n"
assert normalized.count(prune_lines)==1;normalized=normalized.replace(prune_lines,'').replace("json.dumps(manifest, separators=(',', ':'))", 'json.dumps(manifest, indent=2)');assert normalized==old
for n,h in extra.items():assert sha(R/n)==h
catalog=R/'book/coverage/checks/future27-core/closed-checkpoint26-delivery-originals-v2/closed-original-byte-aliases-v1.json';cat=json.loads(catalog.read_bytes());matches=[x for x in cat['aliases'] if x['immutable_original_byte_copy']['file']==newpath];assert len(matches)==1 and matches[0]['immutable_original_byte_copy']=={'file':newpath,'sha256':newhash} and matches[0]['original']=={'file':'reports/full-coverage/pages26-config-previous-original-v1.yml','sha256':newhash}
assert cat['both_actual_pages_runs_and_all31_live_assets_passed'] is True
route=[];active=False
for n in tr.body:
 if isinstance(n,ast.Assert) and ast.unparse(n).startswith('assert re.fullmatch'):active=True
 if active and isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='selected' for t in n.targets):break
 if active:route.append(n)
extra_loop=next(n for n in tr.body if isinstance(n,ast.For) and isinstance(n.iter,ast.Call) and ast.unparse(n.iter).startswith("selection.get('extra_frozen_inputs'"))
prune_loop=next(n for n in tr.body if isinstance(n,ast.For) and isinstance(n.target,ast.Name) and n.target.id=='domain')
fixtures=[]
def runfixture(name,func,accept):
 got=True
 try:func()
 except (AssertionError,ValueError,KeyError,FileNotFoundError):got=False
 assert got==accept,(name,got,accept)
 fixtures.append({'name':name,'expected_accept':accept,'observed_accept':got,'explicit_synthetic_fixture':True,'actual_producer_execution_claimed':False})
with tempfile.TemporaryDirectory(prefix='modules-freezer27-fixtures-') as td:
 F=Path(td);selname='reports/full-coverage/checkpoint-27-selection.json';sp=F/selname;sp.parent.mkdir(parents=True)
 base={'proof_file_count':1175,'new_file_count':8,'proof_files':{'verification/lean/SafeLearning/Synthetic'+str(i)+'.lean':{'sha256':'0'*64} for i in range(1175)},'extra_frozen_inputs':{n:{'sha256':h,'scope':'immutable_audit_or_local_source_evidence'} for n,h in extra.items()}}
 def routing(body=None,selectionname=selname,digest=None,snapshotname='reports/full-coverage/new-fixture',existing=False):
  d=copy.deepcopy(base if body is None else body);dest=F/selectionname;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(json.dumps(d));snap=F/snapshotname
  if existing:snap.mkdir(parents=True,exist_ok=True)
  env={'ROOT':F,'args':SimpleNamespace(selection=Path(selectionname),snapshot=Path(snapshotname),selection_sha256=digest or sha(dest)),'re':re,'sha':sha,'json':json,'CHECKPOINT27_SELECTION':selname,'CHECKPOINT27_EXACT_EXTRA_SUFFIX_EXCEPTIONS':extra}
  exec(compile(ast.Module(body=route,type_ignores=[]),str(H),'exec'),env)
 runfixture('exact reviewed27 path1175/new8 explicit synthetic schema',lambda:routing(),True)
 runfixture('old26 selection routing rejected',lambda:routing(selectionname='reports/full-coverage/checkpoint-26-selection.json'),False)
 runfixture('selection digest mismatch rejected',lambda:routing(digest='0'*64),False)
 runfixture('invalid digest syntax rejected',lambda:routing(digest='bad'),False)
 runfixture('snapshot outside allowed report root rejected',lambda:routing(snapshotname='book/coverage/fake-snapshot'),False)
 runfixture('existing snapshot rejected',lambda:routing(snapshotname='reports/full-coverage/already-exists',existing=True),False)
 for key,value in [('proof_file_count',1167),('new_file_count',11)]:
  b=copy.deepcopy(base);b[key]=value;runfixture('wrong '+key+' rejected',lambda b=b:routing(b),False)
 for n in extra:
  b=copy.deepcopy(base);b['extra_frozen_inputs'].pop(n);runfixture('missing exact suffix exception '+Path(n).name,lambda b=b:routing(b),False)
  b=copy.deepcopy(base);b['extra_frozen_inputs'][n]['sha256']='0'*64;runfixture('mismatched exact suffix digest '+Path(n).name,lambda b=b:routing(b),False)
 def auditentry(n,record):
  env={'ROOT':F,'Path':Path,'sha':sha,'selection':{'extra_frozen_inputs':{n:record}},'CHECKPOINT27_EXACT_EXTRA_SUFFIX_EXCEPTIONS':extra,'files':[]}
  exec(compile(ast.Module(body=[extra_loop],type_ignores=[]),str(H),'exec'),env);assert env['files']==[n]
 for suffix in ['.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt']:
  n='book/coverage/synthetic-evidence'+suffix;p=F/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'explicit synthetic fixture bytes')
  record={'sha256':sha(p),'scope':'immutable_audit_or_local_source_evidence'};runfixture('allowed explicit audit suffix '+suffix,lambda n=n,r=record:auditentry(n,r),True)
 for n,h in extra.items():
  p=F/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((R/n).read_bytes());runfixture('exact pinned archive suffix '+Path(n).name,lambda n=n,h=h:auditentry(n,{'sha256':h,'scope':'immutable_audit_or_local_source_evidence'}),True)
 for suffix in ['.yml','.olean','.png','.bak']:
  n='book/coverage/unapproved'+suffix;p=F/n;p.write_bytes(b'explicit synthetic unapproved archive');runfixture('unapproved archive suffix '+suffix+' rejected',lambda n=n,p=p:auditentry(n,{'sha256':sha(p),'scope':'immutable_audit_or_local_source_evidence'}),False)
 py='book/coverage/synthetic-evidence.py';ph=sha(F/py)
 for n in [str(F/py),'book/coverage/../coverage/synthetic-evidence.py','book//coverage/synthetic-evidence.py','reports/full-coverage/unapproved.py']:
  runfixture('unsafe explicit audit routing '+n,lambda n=n:auditentry(n,{'sha256':ph,'scope':'immutable_audit_or_local_source_evidence'}),False)
 runfixture('wrong explicit scope rejected',lambda:auditentry(py,{'sha256':ph,'scope':'different'}),False)
 runfixture('changed explicit bytes rejected',lambda:auditentry(py,{'sha256':'0'*64,'scope':'immutable_audit_or_local_source_evidence'}),False)
 applied3=['verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean','verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean','verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean']
 source='verification/lean/SafeLearning/SelectedSynthetic.lean'
 def pruning(label,listed_as_list=False,added_domain=None,remove=False,missing_decl=False):
  snap=F/'prune-fixtures'/label
  original={}
  for domain in ['foundations','applied','modules','core']:
   names=[source]+(applied3 if domain=='applied' else [])
   if added_domain==domain:names.append('verification/lean/SafeLearning/UnapprovedMetadata.lean')
   if remove and domain=='applied':names.remove(applied3[-1])
   d={'exercises':[{'claims':[{'lean_declarations':['MISSING' if missing_decl else 'T']}]}],'material_claims':[],'proof_files':names if listed_as_list else {n:'originalhash' for n in names},'proof_sha256':{n:'originalhash' for n in names},'original_math_body_time':'unchanged'}
   p=snap/f'book/coverage/{domain}.json';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d));original[domain]=copy.deepcopy(d)
  env={'snapshot':snap,'json':json,'declarations':{'T'},'selected':{source:{}},'excluded_metadata':{}}
  exec(compile(ast.Module(body=[prune_loop],type_ignores=[]),str(H),'exec'),env)
  assert env['excluded_metadata']=={'foundations':[],'applied':applied3,'modules':[],'core':[]}
  for domain in ['foundations','applied','modules','core']:
   actual=json.loads((snap/f'book/coverage/{domain}.json').read_bytes());expected=copy.deepcopy(original[domain])
   if domain=='applied':expected['proof_files']=[source] if listed_as_list else {source:'originalhash'};expected['proof_sha256']={source:'originalhash'}
   assert actual==expected
 runfixture('exact Applied3 pruning dictionary preserving all bodies/time',lambda:pruning('dictionary'),True)
 runfixture('exact Applied3 pruning list and parallel hash map',lambda:pruning('list',listed_as_list=True),True)
 for domain in ['foundations','applied','modules','core']:runfixture('unexpected '+domain+' metadata rejected',lambda domain=domain:pruning('extra-'+domain,added_domain=domain),False)
 runfixture('missing one expected Applied metadata rejected',lambda:pruning('missing',remove=True),False)
 runfixture('unselected claim declaration rejected',lambda:pruning('claim-gap',missing_decl=True),False)
 example={'status':'frozen_inputs_not_yet_aggregate_verified','proof_files':base['proof_files'],'working_inputs_sha256':{'a':'b'},'excluded_unreferenced_ledger_metadata':{'applied':applied3},'coverage_complete':False}
 assert json.loads(json.dumps(example,indent=2))==json.loads(json.dumps(example,separators=(',',':')))
 fixtures.append({'name':'compact serialization retains entire manifest JSON value and unverified status','expected_accept':True,'observed_accept':True,'explicit_synthetic_fixture':True,'actual_producer_execution_claimed':False})
finding=Path('/tmp/checkpoint27-freezer1-independent-modules-requires-changes-v1.json');assert not finding.exists();finding.write_text(json.dumps({'status':'requires_changes','errors':['CHECKPOINT27_SELECTION points to actual26 selection while counts require1175/new8; no27 path can pass.'],'helper':ref(V1),'helper_sha256':sha(V1),'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'review_kind':'read_only_code_finding','producer_execution_claimed':False,'resolution':'New v2 changes only the pinned selection literal from26 to27; original v1 remains exact and unexecuted.'},indent=2)+'\n')
closed={ref(x)['file']:sha(x) for x in [H,V1,OLD,catalog,finding]};closed.update(extra)
d={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(H),'helper_sha256':sha(H),'original_unexecuted_v1_finding':ref(finding),'helpers_sha256':{ref(H)['file']:sha(H),ref(V1)['file']:sha(V1),ref(OLD)['file']:sha(OLD)},'exact_v2_to_v1_delta':'Only selection filename26→27. Original v1 retained with explicit read-only requires-changes decision.','full_reverse_to_exact26_restores_all_original_guard_copy_and_aggregate_flows':True,'selection_sources':1175,'new_sources':8,'exact_suffix_exception_count':7,'exact_suffix_exceptions':extra,'new_yaml_bound_to_actual_closed26_delivery_catalog':ref(catalog),'expected_excluded_metadata':{'foundations':[],'core':[],'modules':[],'applied':applied3},'fixture_count':len(fixtures),'fixtures':fixtures,'compact_manifest_serialization_preserves_entire_JSON_body':True,'actual_freeze_or_aggregate_claim':False,'closed_evidence_sha256':closed,'scope':'Independent full source/delta and isolated routing/suffix/pruning tests of actual AST fragments, with all seven real archive hashes and native closed26 alias catalog checked. Fixtures are explicit synthetic code tests; no actual27 selection/freeze/aggregate or owner writes.'}
with OUT.open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps({'status':'passed','result':ref(OUT),'fixtures':len(fixtures)}))
