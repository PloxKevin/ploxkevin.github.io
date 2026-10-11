from pathlib import Path
from datetime import datetime,timezone
import ast,contextlib,copy,hashlib,io,json,shutil,sys,tempfile
R=Path('/home/oxrexkevin/SafetyBased');NEW=R/'book/coverage/freeze_checkpoint28_v1.py';OLD=R/'book/coverage/freeze_checkpoint27_v2.py';OUT=Path('/tmp/freeze28-independent-modules28-reader-v1.json');START=datetime.now(timezone.utc).isoformat()
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':h(p)}
assert h(NEW)=='545d20ddc9cb15c35f93297da01c6f7ecdfc9ab64b8eb351f379e580698e3607'
assert h(OLD)=='4c964b933eac26217b6965efb9b5f4e27649402f63b0a77662de0b5692af0e14'
old,new=OLD.read_text(),NEW.read_text()
expected=old.replace('CHECKPOINT27','CHECKPOINT28').replace('checkpoint-27-selection.json','checkpoint-28-selection.json').replace('checkpoint27 selection bytes','checkpoint28 selection bytes').replace('== 1175','== 1186').replace('== 8\n','== 11\n').replace("files += ['book/inventory_claims.py', 'book/validate.py']","files += ['book/inventory_claims.py', 'book/validate.py', 'book/validate28_v1.py', 'book/chapters/lipsdp.html']")
assert expected==new and len(new.splitlines())==len(old.splitlines())==180
def constant(source,name):
 return next(ast.literal_eval(n.value) for n in ast.parse(source).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets))
exceptions=constant(new,'CHECKPOINT28_EXACT_EXTRA_SUFFIX_EXCEPTIONS');assert exceptions==constant(old,'CHECKPOINT27_EXACT_EXTRA_SUFFIX_EXCEPTIONS') and len(exceptions)==7
unused=['verification/lean/SafeLearning/CompleteAppliedBinaryTemperaturePrecision.lean','verification/lean/SafeLearning/CompleteAppliedBinaryVariationalPrecision.lean','verification/lean/SafeLearning/CompleteAppliedConformalCalibrationOnly.lean']
assert str(unused) in new
tree=ast.parse(new);root_nodes=[n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='ROOT' for t in n.targets)];assert len(root_nodes)==1
tree.body.remove(root_nodes[0]);code=compile(ast.fix_missing_locations(tree),str(NEW),'exec')
sys.path.insert(0,str(R/'book/coverage'))
TMP=Path(tempfile.mkdtemp(prefix='freeze28-independent-modules28-'));BASE=TMP/'base';BASE.mkdir()
def write(root,n,b):
 p=root/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return p
selected={}
for j in range(1186):
 n=f'verification/lean/SafeLearning/Fixture{j}.lean';p=write(BASE,n,f'namespace Fixture{j}\ntheorem item : True := by trivial\nend Fixture{j}\n'.encode());selected[n]={'sha256':h(p),'evidence_sha256':{}}
for domain in ['foundations','applied','modules','core']:
 ledger={'exercises':[],'material_claims':[],'proof_files':unused if domain=='applied' else []}
 write(BASE,'book/coverage/'+domain+'.json',(json.dumps(ledger)+'\n').encode())
extras={}
for n,s in exceptions.items():
 assert h(R/n)==s;write(BASE,n,(R/n).read_bytes());extras[n]={'sha256':s,'scope':'immutable_audit_or_local_source_evidence'}
for n in ['book/inventory_claims.py','book/validate.py','book/validate28_v1.py','book/chapters/lipsdp.html','verification/lean/lean-toolchain','verification/lean/lakefile.toml','verification/lean/lake-manifest.json','verification/lean/verify.py','qa/learning_review.mjs','qa/book_browser_checks.mjs']:
 write(BASE,n,(R/n).read_bytes())
write(BASE,'SafeLearning/fixture.html',b'<html>isolated code fixture</html>\n')
(BASE/'verification/lean/.lake/packages').mkdir(parents=True)
selection={'proof_file_count':1186,'new_file_count':11,'proof_files':selected,'extra_frozen_inputs':extras}
def invoke(label,mutate=None,expected_failure=None,wrong_hash=False,wrong_selection=False,existing=False,escape=False,copy_race=False):
 root=TMP/label;shutil.copytree(BASE,root);s=copy.deepcopy(selection)
 if mutate:mutate(root,s)
 sp=write(root,'reports/full-coverage/checkpoint-28-selection.json',(json.dumps(s)+'\n').encode())
 snap='reports/full-coverage/snapshot'
 if existing:(root/snap).mkdir()
 if escape:snap='outside-snapshot'
 original_argv=sys.argv;sys.argv=['freeze_checkpoint28_v1.py','--selection','reports/full-coverage/checkpoint-27-selection.json' if wrong_selection else 'reports/full-coverage/checkpoint-28-selection.json','--snapshot',snap,'--selection-sha256','0'*64 if wrong_hash else h(sp)]
 if wrong_selection:write(root,'reports/full-coverage/checkpoint-27-selection.json',sp.read_bytes())
 original_copy=shutil.copyfile
 if copy_race:
  done=[False]
  def changed_copy(src,dst,*args,**kwargs):
   result=original_copy(src,dst,*args,**kwargs)
   if not done[0] and Path(src)==root/'verification/lean/SafeLearning/Fixture0.lean':done[0]=True;Path(src).write_bytes(Path(src).read_bytes()+b'-- changed during copying\n')
   return result
  shutil.copyfile=changed_copy
 log=io.StringIO();failure=None
 try:
  with contextlib.redirect_stdout(log):exec(code,{'ROOT':root,'__file__':str(NEW),'__name__':'__main__'})
 except (AssertionError,ValueError,FileNotFoundError) as e:failure={'exception':type(e).__name__,'message':str(e)}
 finally:sys.argv=original_argv;shutil.copyfile=original_copy
 if expected_failure:
  assert failure is not None,label
  if expected_failure!='assert':assert expected_failure in failure['message'],(label,failure)
  return {'case':label,'rejected':True,'actual_failure':failure}
 assert failure is None,(label,failure)
 manifest=json.loads((root/'reports/full-coverage/snapshot-manifest.json').read_bytes())
 assert manifest['status']=='frozen_inputs_not_yet_aggregate_verified' and manifest['coverage_complete'] is False and len(manifest['proof_files'])==1186
 assert manifest['excluded_unreferenced_ledger_metadata']=={'foundations':[],'core':[],'modules':[],'applied':unused}
 for n in ['book/validate28_v1.py','book/chapters/lipsdp.html']:
  assert manifest['working_inputs_sha256'][n]==manifest['frozen_inputs_sha256'][n]==h(root/n)
 assert all(manifest['working_inputs_sha256'][n]==manifest['frozen_inputs_sha256'][n]==digest for n,digest in exceptions.items())
 assert h(root/'verification/lean/SafeLearning/Fixture0.lean')==manifest['frozen_inputs_sha256']['verification/lean/SafeLearning/Fixture0.lean']
 return {'case':label,'passed':True,'frozen_sources':1186,'new_explicit_frozen_inputs':['book/validate28_v1.py','book/chapters/lipsdp.html'],'seven_exact_archive_bytes_frozen':True,'only_three_expected_unused_metadata_removed':True,'log':log.getvalue()}
positive=invoke('exact-full-helper-positive')
fixtures=[]
fixtures.append(invoke('wrong-reviewed-selection-digest',wrong_hash=True,expected_failure='exact reviewed checkpoint28'))
fixtures.append(invoke('old27-selection-name',wrong_selection=True,expected_failure='exact reviewed checkpoint28'))
fixtures.append(invoke('old1175-count',lambda r,s:s.update(proof_file_count=1175),expected_failure='assert'))
fixtures.append(invoke('old8-new-file-count',lambda r,s:s.update(new_file_count=8),expected_failure='assert'))
fixtures.append(invoke('existing-snapshot',existing=True,expected_failure='new snapshot directory'))
fixtures.append(invoke('snapshot-outside-allowed-root',escape=True,expected_failure='new snapshot directory'))
fixtures.append(invoke('pinned-archive-missing',lambda r,s:s['extra_frozen_inputs'].pop(next(iter(exceptions))),expected_failure='exact archive exception differs'))
fixtures.append(invoke('pinned-archive-digest-changed',lambda r,s:s['extra_frozen_inputs'][next(iter(exceptions))].update(sha256='0'*64),expected_failure='exact archive exception differs'))
fixtures.append(invoke('selected-source-changed',lambda r,s:(r/'verification/lean/SafeLearning/Fixture0.lean').write_text('-- changed\n'),expected_failure='Selected source changed'))
def missing_dependency(r,s):
 p=r/'verification/lean/SafeLearning/Fixture0.lean';p.write_text('import SafeLearning.Absent\n'+p.read_text());s['proof_files']['verification/lean/SafeLearning/Fixture0.lean']['sha256']=h(p)
fixtures.append(invoke('selected-dependency-missing',missing_dependency,expected_failure='Missing selected dependency'))
def bad_evidence(r,s):s['proof_files']['verification/lean/SafeLearning/Fixture0.lean']['evidence_sha256']['/tmp/foreign-evidence.json']='0'*64
fixtures.append(invoke('absolute-selected-evidence',bad_evidence,expected_failure='Selected evidence escapes'))
def extra_archive(r,s):
 original=next(iter(exceptions));n='book/coverage/checks/foreign.olean';write(r,n,(r/original).read_bytes());s['extra_frozen_inputs'][n]={'sha256':h(r/n),'scope':'immutable_audit_or_local_source_evidence'}
fixtures.append(invoke('unlisted-fourth-olean',extra_archive,expected_failure='Invalid or changed explicit audit input'))
def extra_unused(r,s):
 p=r/'book/coverage/applied.json';d=json.loads(p.read_bytes());d['proof_files'].append('verification/lean/SafeLearning/ForeignUnused.lean');p.write_text(json.dumps(d))
fixtures.append(invoke('fourth-unused-applied-metadata',extra_unused,expected_failure='Unexpected excluded metadata'))
def unmapped_claim(r,s):
 p=r/'book/coverage/modules.json';d=json.loads(p.read_bytes());d['material_claims'].append({'lean_declarations':['Absent.statement']});p.write_text(json.dumps(d))
fixtures.append(invoke('claim-declaration-missing',unmapped_claim,expected_failure='selected files omit claim references'))
fixtures.append(invoke('source-changes-during-copy',copy_race=True,expected_failure='Working inputs changed during freezing'))
assert not OUT.exists()
d={'status':'passed_independent_freeze28_full_code_and_exact27_delta_review','errors':[],'helper':ref(NEW),'approved_original27_helper':ref(OLD),'reader_started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'full180_lines_read':True,'exact_delta_reconstruction':True,'exact_seven_suffix_exception_map_unchanged':exceptions,'exact_three_unused_applied_metadata_unchanged':unused,'positive_actual_full_helper_execution':positive,'meaningful_actual_full_helper_negative_fixtures':fixtures,'isolated_fixture_root':str(TMP),'fixture_source_scope':'Synthetic1186 metadata/source fixtures exercise actual freezer control flow; no Lean proof or production checkpoint claim. All seven allowed archive fixture bytes are exact real archived bytes. Actual helper ROOT and snapshot are relocated to TMP.','production_selection_or_snapshot_executed':False,'production_owner_source_selection_or_publication_written':False,'coverage_complete':False}
OUT.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'reader':ref(OUT),'negative_fixtures':len(fixtures),'production_freeze_executed':False}))
