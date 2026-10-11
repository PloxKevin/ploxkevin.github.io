from pathlib import Path
import copy,hashlib,importlib.util,json,sys,tempfile
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'))
spec=importlib.util.spec_from_file_location('selector22',R/'book/coverage/prepare_checkpoint22_selection.py')
h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(R/'book/coverage/retain_baseline_inputs22.py')==sha(R/'book/coverage/retain_baseline_inputs21.py')=='a6d122cfc0000360185acf9628693d4e041eefe0ed8b96e0f0bff5fb047859d1'
ready=R/'book/coverage/checks/future22-monitoring/core22-proof-evidence-readiness-v1.json'
assert sha(ready)=='7e5dc9887050a795c8a31d4e47091a32336b349646083077fcf59b7f2d333fd7'
real=json.loads(ready.read_text());matches=[]
for source,row in real['proof_files'].items():matches.append(h.standalone_success(source,row['sha256'],row['evidence_sha256']))
assert len(matches)==14
real_source='verification/lean/SafeLearning/CompleteModulesNNScalarPractices22.lean'
offer=json.loads((R/'book/coverage/checks/modules-future22/source48/modules-audit22-candidate-source48-additions-v2-reviewed.json').read_text())
row=offer['proof_files'][real_source]
real_nn=h.standalone_success(real_source,row['sha256'],row['evidence_sha256'])
geometry_source='verification/lean/SafeLearning/CompleteModulesNNGeometryPractices22.lean'
combined=json.loads((R/'book/coverage/checks/modules-future22/source48/modules-audit22-candidate-source48-additions-v3.json').read_text())
g=combined['proof_files'][geometry_source]
real_geometry=h.standalone_success(geometry_source,g['sha256'],g['evidence_sha256'])
passed=[]
with tempfile.TemporaryDirectory(prefix='selector22-guard-fixtures-') as temp:
 root=Path(temp);h.ROOT=root;source=real_source;path=root/source;path.parent.mkdir(parents=True);path.write_bytes((R/source).read_bytes());digest=sha(path)
 good={'source':source,'source_sha256_before':digest,'source_sha256_after':digest,'source_unchanged':True,'actual_exit_code':0,'command':['lake','env','lean','SafeLearning/'+Path(source).name],'actual_workdir':str(root/'verification/lean'),'log_sha256':hashlib.sha256(b'fixture log\n').hexdigest(),'source_snapshot_sha256':digest,'scope':'SYNTHETIC guard fixture; no new compiler execution asserted.'}
 named=copy.deepcopy(good);named['command']=['lake','build','SafeLearning.'+Path(source).stem]
 def trial(label,mutate=None,accept=False):
  s=copy.deepcopy(good);n=copy.deepcopy(named);options={'include_log':True,'include_named':True}
  if mutate:mutate(s,n,options)
  d=root/'fixtures'/label;d.mkdir(parents=True)
  (d/'standalone.json').write_text(json.dumps(s));(d/'named.json').write_text(json.dumps(n));(d/'original-content-alias.log').write_bytes(b'fixture log\n')
  evidence={str((d/'standalone.json').relative_to(root)):sha(d/'standalone.json')}
  if options['include_named']:evidence[str((d/'named.json').relative_to(root))]=sha(d/'named.json')
  if options['include_log']:evidence[str((d/'original-content-alias.log').relative_to(root))]=sha(d/'original-content-alias.log')
  try:h.standalone_success(source,digest,evidence);actual=True
  except (AssertionError,KeyError,ValueError):actual=False
  assert actual==accept,(label,actual,accept)
  passed.append({'fixture':label,'expected_acceptance':accept,'actual_acceptance':actual})
 trial('actual_exit_alias',accept=True)
 trial('exit_alias',lambda s,n,o:[(r.pop('actual_exit_code'),r.update(exit_code=0)) for r in [s,n]],True)
 trial('missing_source_unchanged_derived_from_exact_before_after',lambda s,n,o:[r.pop('source_unchanged') for r in [s,n]],True)
 trial('lean_file_source_alias',lambda s,n,o:[r.update(lean_file=r.pop('source')) for r in [s,n]],True)
 trial('original_named_lean_o_alias',lambda s,n,o:n.update(command=['lake','env','lean','-o','/tmp/exact-original-module.olean','SafeLearning/'+Path(source).name]),True)
 trial('original_tmp_input_snapshot_alias',lambda s,n,o:s.update(source='/tmp/'+Path(source).name,command=['lake','env','lean','/tmp/'+Path(source).name]),True)
 trial('contradictory_exit_aliases',lambda s,n,o:s.update(exit_code=1),False)
 trial('failed_named_execution',lambda s,n,o:n.update(actual_exit_code=1),False)
 trial('stale_source_before_sha',lambda s,n,o:s.update(source_sha256_before='0'*64),False)
 trial('stale_source_after_sha',lambda s,n,o:s.update(source_sha256_after='0'*64),False)
 trial('explicit_source_changed_false',lambda s,n,o:s.update(source_unchanged=False),False)
 trial('missing_raw_log_alias',lambda s,n,o:o.update(include_log=False),False)
 trial('wrong_actual_cwd',lambda s,n,o:s.update(actual_workdir=str(root)),False)
 trial('named_not_a_standalone_substitute',lambda s,n,o:o.update(include_named=False),False)
 trial('wrong_relative_input',lambda s,n,o:s.update(command=['lake','env','lean','SafeLearning/Different.lean']),False)
 trial('wrong_tmp_source_snapshot',lambda s,n,o:s.update(source='/tmp/'+Path(source).name,command=['lake','env','lean','/tmp/'+Path(source).name],source_snapshot_sha256='0'*64),False)
 for unsafe in ['../outside','/absolute','book/./coverage/file','']:
  try:h.safe(unsafe);ok=False
  except AssertionError:ok=True
  assert ok,unsafe
  passed.append({'fixture':'reject_noncanonical_path_'+repr(unsafe),'expected_rejection':True})
h.ROOT=R
out=R/'book/coverage/checks/future22-core/modules-checkpoint22-selection-helper-fixtures-v2.json';out.parent.mkdir(exist_ok=True)
data={'status':'actual_readonly_helper_schema_and_guard_fixtures_passed','checker':str(Path(__file__)),'checker_sha256':sha(__file__),'selection_helper':'book/coverage/prepare_checkpoint22_selection.py','selection_helper_sha256':sha(R/'book/coverage/prepare_checkpoint22_selection.py'),'retainer22':'book/coverage/retain_baseline_inputs22.py','retainer22_sha256':sha(R/'book/coverage/retain_baseline_inputs22.py'),'retainer_is_byte_identical_to_reviewed21':True,'real_original_root_and_growing_sources_checked':14,'real_original_nn_sources_checked':2,'real_exact_standalone_record_matches':matches+[real_nn,real_geometry],'guard_fixtures':passed,'scope':'Only helper guard/schema fixtures and original existing source evidence reads were executed. No production plan, selection22 or retained21 input map was produced; no synthetic fixture is offered as a compiler success.','errors':[]}
with out.open('x') as f:f.write(json.dumps(data,indent=2)+'\n')
print(json.dumps({'report':str(out.relative_to(R)),'sha256':sha(out),'real_sources':16,'synthetic_guard_fixtures':len(passed)}))
