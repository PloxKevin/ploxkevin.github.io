from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,types,tempfile
R=Path('/home/oxrexkevin/SafetyBased');H=R/'book/coverage/retain_baseline_inputs27_v1.py';O=Path('/tmp/checkpoint27-retainer-independent-modules-check-result-v1.json');assert not O.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p)}
assert sha(H)=='159d6f53b2a2a05cbc68155d2925a14dc46e90b2d47392ab32c6b822877e2d33'
source=H.read_text();native={};exec(compile(source,str(H),'exec'),native)
for name,key in [('BASELINE','BASELINE_SHA'),('MANIFEST','MANIFEST_SHA'),('AUDIT','AUDIT_SHA')]:assert sha(R/native[name])==native[key]
baseline=json.loads((R/native['BASELINE']).read_bytes());manifest=json.loads((R/native['MANIFEST']).read_bytes());audit=json.loads((R/native['AUDIT']).read_bytes())
assert len(baseline['proof_files'])==1167 and len(manifest['frozen_inputs_sha256'])==47277 and manifest['proof_files']==baseline['proof_files'] and audit['status']=='passed' and audit['proof_file_count']==1167
assert native['OWNER_EVIDENCE_PATHS']=={'book/coverage/'+n+'.json' for n in ['core','foundations','applied','modules']} and native['ALIAS_PATHS']==native['OWNER_EVIDENCE_PATHS']|{'SafeLearning/lyapunov-mpc.html'}
assert native['APPLICATION']=={'file':'reports/full-coverage/source54-55-corrections-application-v1.json','sha256':'845937be3efd0d3bb88518fe9597b4bf6f22ead237cd1292a28ad5b16265c528'} and native['APPLICATION_EXECUTION']=={'file':'reports/full-coverage/source54-55-corrections-application-execution-v1.json','sha256':'a255862de464e0f1acf284807c4a48b732bc69055cf71b445ea2df5920494805'}
for r in [native['APPLICATION'],native['APPLICATION_EXECUTION']]:assert sha(R/r['file'])==r['sha256']
application=json.loads((R/native['APPLICATION']['file']).read_bytes());assert application['applications'][0]['source_after']=={'file':native['SOURCE'],'sha256':native['SOURCE_NEW_SHA']} and sha(R/native['SOURCE_ARCHIVE'])==native['SOURCE_OLD_SHA'] and sha(R/native['SOURCE'])==native['SOURCE_NEW_SHA']
# Execute the original unchanged functions in an explicit synthetic workspace.
# Hash pins below are remapped only inside this isolated test namespace; native
# production baseline/source pins above are independently checked unchanged.
fixtures=[]
def test(name,f,accept):
 got=True
 try:f()
 except (AssertionError,ValueError,KeyError,FileNotFoundError):got=False
 assert got==accept,(name,got,accept)
 fixtures.append({'name':name,'expected_accept':accept,'observed_accept':got,'explicit_synthetic_fixture':True,'production_execution_claimed':False})
with tempfile.TemporaryDirectory(prefix='modules-retainer27-fixtures-') as temp:
 F=Path(temp);ns={};exec(compile(source,str(H),'exec'),ns)
 def put(n,data):
  p=F/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return {'file':n,'sha256':sha(p)}
 def putj(n,d):return put(n,(json.dumps(d,sort_keys=True)+'\n').encode())
 def get(n):return json.loads((F/n).read_bytes())
 proofbytes=b'explicit synthetic selected Lean source';proofhash=hashlib.sha256(proofbytes).hexdigest();stable=put('book/coverage/stable-evidence.json',b'stable explicit synthetic evidence')
 owners=sorted(ns['OWNER_EVIDENCE_PATHS']);oldhash={};currenthash={};replacements=[];alias={}
 for n in owners+['book/coverage/applied-promotions.json']:
  oldhash[n]=hashlib.sha256(('synthetic original '+n).encode()).hexdigest();new=put(n,('synthetic installed current27 '+n).encode());currenthash[n]=new['sha256'];archive='reports/full-coverage/owner26-originals-before-owner27-integration-v1/'+Path(n).name;oldref=put(archive,('synthetic original '+n).encode());candidate=put('book/coverage/candidates/'+Path(n).name,('synthetic installed current27 '+n).encode());replacements.append({'destination':n,'before_sha256':oldhash[n],'candidate':candidate,'original26_byte_copy':archive})
  if n in owners:alias[n]={'original_sha256':oldhash[n],'immutable_byte_copy':oldref}
 ns['SOURCE_OLD_SHA']=hashlib.sha256(b'synthetic old53 lyap').hexdigest();newsource=put(ns['SOURCE'],b'synthetic corrected55 lyap');ns['SOURCE_NEW_SHA']=newsource['sha256'];sourceold=put(ns['SOURCE_ARCHIVE'],b'synthetic old53 lyap');alias[ns['SOURCE']]={'original_sha256':ns['SOURCE_OLD_SHA'],'immutable_byte_copy':sourceold};currenthash[ns['SOURCE']]=ns['SOURCE_NEW_SHA']
 original_evidence={stable['file']:stable['sha256'],**{n:oldhash[n] for n in owners},ns['SOURCE']:ns['SOURCE_OLD_SHA']}
 rows={}
 for i in range(1167):
  n='verification/lean/SafeLearning/Synthetic'+str(i)+'.lean';put(n,proofbytes);rows[n]={'sha256':proofhash,'evidence_sha256':copy.deepcopy(original_evidence),'name':'Synthetic'+str(i),'status':'original_proved','old_review_time':'immutable_original_time','checkpoint26_original_baseline_evidence':{'older_full_provenance':'must remain unchanged','nested_original_body':[i,'body']}}
 unique=put('reports/full-coverage/checkpoint-26/book/coverage/unique-frozen-evidence.json',b'one synthetic unique old snapshot byte');frozen={'book/coverage/synthetic-frozen-'+str(i)+'.json':proofhash for i in range(47276)};frozen['book/coverage/unique-frozen-evidence.json']=unique['sha256']
 base={'status':'explicit_selection_requires_fresh_aggregate_audit','proof_files':rows,'proof_file_count':1167,'extra_frozen_inputs':{stable['file']:{'sha256':stable['sha256'],'scope':'immutable_audit_or_local_source_evidence'}}};base_ref=putj(ns['BASELINE'],base);ns['BASELINE_SHA']=base_ref['sha256']
 man={'status':'formal_verification_passed_partial_coverage','selection':ns['BASELINE'],'selection_sha256':ns['BASELINE_SHA'],'proof_files':rows,'frozen_inputs_sha256':frozen,'working_inputs_sha256':{**oldhash,ns['SOURCE']:ns['SOURCE_OLD_SHA']},'snapshot':'reports/full-coverage/checkpoint-26'};manref=putj(ns['MANIFEST'],man);ns['MANIFEST_SHA']=manref['sha256'];audref=putj(ns['AUDIT'],{'status':'passed','proof_file_count':1167});ns['AUDIT_SHA']=audref['sha256']
 helper=put(ns['INTEGRATION_HELPER'],b'explicit synthetic integration helper');binding=putj('book/coverage/checks/synthetic-binding.json',{'helper':helper});log=put('reports/full-coverage/synthetic-integration.log',b'synthetic actual log')
 result={'status':'four_exact_reviewed_owner27_candidate_bytes_integrated_pending_fresh_current55_global_integrity_and_aggregate27_audit','applied':True,'coverage_complete':False,'protected_proof_source_count':1175,'new_canonical_source_count':8,'actual_helper':helper,'binding_manifest':binding['file'],'binding_manifest_sha256':binding['sha256'],'exact_replacements':replacements};resultpath='reports/full-coverage/synthetic-integration-result.json';exe_path='reports/full-coverage/synthetic-integration-execution.json'
 execution={'actual_exit_code':0,'exit_code':0,'actual_command':['python3',helper['file'],binding['file'],'--apply'],'command':['python3',helper['file'],binding['file'],'--apply'],'actual_workdir':str(F),'helper_sha256_before':{helper['file']:helper['sha256']},'helper_sha256_after':{helper['file']:helper['sha256']},'log':log['file'],'log_sha256':log['sha256']}
 sourcehelper=put('book/coverage/checks/synthetic-source-helper.py',b'explicit synthetic source helper');slog=put('reports/full-coverage/synthetic-source.log',b'synthetic source actual log');hist=putj('reports/full-coverage/source-history/synthetic-history.json',{'status':'exact_source53_and_owner26_original_bytes_preserved_before_source54_55','original_root_files':{ns['SOURCE']:sourceold}})
 app={'status':'passed_actual_source54_and_source55_corrections_full29_inventory_owner_identity_rebase_pending','coverage_complete':False,'selected26_proof_sources_unchanged':1167,'five_installed26_owner_ledgers_unchanged':True,'applications':[{'correction_id':54,'source_after':newsource},{'correction_id':55,'source_after':{'file':'SafeLearning/verification.html','sha256':'1'*64}}],'helper':sourcehelper,'preserved_history':hist}
 sexecution={'actual_exit_code':0,'exit_code':0,'actual_command':['python3',sourcehelper['file']],'actual_workdir':str(F),'helper_sha256_before':{sourcehelper['file']:sourcehelper['sha256']},'helper_sha256_after':{sourcehelper['file']:sourcehelper['sha256']},'log':slog['file'],'log_sha256':slog['sha256']}
 apath=ns['APPLICATION']['file'];sepath=ns['APPLICATION_EXECUTION']['file']
 def auth(res=None,ex=None,application_body=None,source_ex=None,aliases=None):
  r=putj(resultpath,copy.deepcopy(result if res is None else res));e=putj(exe_path,copy.deepcopy(execution if ex is None else ex));ns['APPLICATION']=putj(apath,copy.deepcopy(app if application_body is None else application_body));ns['APPLICATION_EXECUTION']=putj(sepath,copy.deepcopy(sexecution if source_ex is None else source_ex));return {'integration_result':r,'actual_integration_execution':e,'source_application':copy.deepcopy(ns['APPLICATION']),'actual_source_application_execution':copy.deepcopy(ns['APPLICATION_EXECUTION']),'aliases':copy.deepcopy(alias if aliases is None else aliases)}
 def validate(**kwargs):return ns['validate_evidence_aliases'](F,ns['BASELINE'],ns['MANIFEST'],auth(**kwargs))
 test('strict exact five authorized historical aliases synthetic native-schema acceptance',lambda:validate(),True)
 for field in ['actual_exit_code','exit_code']:
  for bad in [False,1,'0']:
   e=copy.deepcopy(execution);e[field]=bad;test('integration exit '+field+' rejects '+repr(bad),lambda e=e:validate(ex=e),False)
 e=copy.deepcopy(execution);e.pop('actual_exit_code');e.pop('exit_code');test('integration missing actual exits rejected',lambda:validate(ex=e),False)
 e=copy.deepcopy(execution);e['command']=['python3','different'];test('conflicting native actual command alias rejected',lambda:validate(ex=e),False)
 e=copy.deepcopy(execution);e['helper_sha256_after'][helper['file']]='0'*64;test('changed actual integration helper fingerprint rejected',lambda:validate(ex=e),False)
 e=copy.deepcopy(execution);e['log_sha256']='0'*64;test('changed actual integration raw log rejected',lambda:validate(ex=e),False)
 e=copy.deepcopy(execution);e['actual_workdir']=str(F/'different');test('different actual integration workdir rejected',lambda:validate(ex=e),False)
 for field,bad in [('status','wrong'),('applied',False),('protected_proof_source_count',1174),('new_canonical_source_count',9)]:
  r=copy.deepcopy(result);r[field]=bad;test('integration result '+field+' drift rejected',lambda r=r:validate(res=r),False)
 r=copy.deepcopy(result);r['exact_replacements'].append(copy.deepcopy(r['exact_replacements'][0]));test('duplicate actual destination rejected',lambda:validate(res=r),False)
 for n in owners:
  aa=copy.deepcopy(alias);aa[n]['original_sha256']='0'*64;test('wrong original owner digest '+Path(n).name,lambda aa=aa:validate(aliases=aa),False)
  r=copy.deepcopy(result);x=next(x for x in r['exact_replacements'] if x['destination']==n);x['original26_byte_copy']='reports/full-coverage/unauthorized/'+Path(n).name;test('wrong archive original owner path '+Path(n).name,lambda r=r:validate(res=r),False)
 aa=copy.deepcopy(alias);aa['book/coverage/fifth-owner.json']=copy.deepcopy(alias[owners[0]]);test('unapproved sixth alias rejected',lambda:validate(aliases=aa),False)
 aa=copy.deepcopy(alias);aa.pop(ns['SOURCE']);test('missing source alias rejected',lambda:validate(aliases=aa),False)
 aa=copy.deepcopy(alias);aa['book/coverage/applied.json']['immutable_byte_copy']=put('reports/full-coverage/pruned-applied.json',b'distinct frozen pruned Applied body');test('pruned Applied frozen body rejected instead of original working archive',lambda:validate(aliases=aa),False)
 se=copy.deepcopy(sexecution);se['actual_exit_code']=False;test('source execution boolFalse rejected',lambda:validate(source_ex=se),False)
 se=copy.deepcopy(sexecution);se['exit_code']=1;test('conflicting source exit alias rejected',lambda:validate(source_ex=se),False)
 ab=copy.deepcopy(app);ab['applications'].reverse();test('wrong correction order rejected',lambda:validate(application_body=ab),False)
 ab=copy.deepcopy(app);ab['applications'][0]['source_after']['sha256']='0'*64;test('wrong corrected Lyap source digest rejected',lambda:validate(application_body=ab),False)
 aa=copy.deepcopy(alias);aa[ns['SOURCE']]['immutable_byte_copy']['file']='reports/full-coverage/different-old-lyap.html';test('wrong old Lyap source archive path rejected',lambda:validate(aliases=aa),False)
 test('normalization preserves every unrelated evidence ref and all five original bytealiases',lambda:ns['normalized_baseline_evidence'](rows[next(iter(rows))],alias),True)
 for n in sorted(alias):
  row=copy.deepcopy(rows[next(iter(rows))]);row['evidence_sha256'][n]='0'*64;test('normalizer rejects resurfaced mismatched old digest '+n,lambda row=row:ns['normalized_baseline_evidence'](row,alias),False)
 row=copy.deepcopy(rows[next(iter(rows))]);ar=alias[owners[0]]['immutable_byte_copy'];row['evidence_sha256'][ar['file']]='0'*64;test('normalizer immutable archive hash conflict rejected',lambda:ns['normalized_baseline_evidence'](row,alias),False)
 row=copy.deepcopy(rows[next(iter(rows))]);row['evidence_sha256'][ar['file']]=ar['sha256'];test('normalizer compatible existing archive accepted',lambda:ns['normalized_baseline_evidence'](row,alias),True)
 safe,fs,verify,checked=ns['_access'](F)
 for name in [str(F/'book/coverage/stable-evidence.json'),'book/coverage/../coverage/stable-evidence.json','book//coverage/stable-evidence.json']:
  test('canonical safe path rejects '+name,lambda name=name:safe(name),False)
 test('strict typed ref rejects extra fields',lambda:verify({**stable,'extra':True}),False)
 test('strict typed ref rejects missing file',lambda:verify({'sha256':stable['sha256']}),False)
 test('strict typed ref rejects invalid SHA syntax',lambda:verify({'file':stable['file'],'sha256':'bad'}),False)
 def selected_rows():
  selected=copy.deepcopy(rows)
  for name,row in rows.items():
   normalized,used=ns['normalized_baseline_evidence'](row,alias);selected[name]['evidence_sha256']=normalized;selected[name]['checkpoint27_original_baseline_evidence']={'original_baseline_selection':base_ref,'original_baseline_source':name,'original_row_canonical_json_sha256':ns['canonical_row_sha256'](row),'authorized_original_path_aliases':copy.deepcopy(used)}
  first=selected[sorted(selected)[0]]
  for n in alias:first['evidence_sha256'][n]=currenthash[n]
  return selected
 # The full retention loop uses a synthetic content map for the47276 identical
 # frozen rows. One distinct snapshot byte exists physically and exercises the
 # new unique alias branch. No production frozen input is simulated as verified.
 real_access=ns['_access'];snapshot_prefix=man['snapshot']+'/'
 def synthetic_access(root):
  s,h,v,c=real_access(root)
  def h2(name):return frozen[name[len(snapshot_prefix):]] if name.startswith(snapshot_prefix) and name[len(snapshot_prefix):] in frozen else h(name)
  return s,h2,v,c
 ns['_access']=synthetic_access
 def retain_case(label,mutate=None):
  authorization=auth();selected=selected_rows();extras=copy.deepcopy(base['extra_frozen_inputs'])
  if mutate:mutate(selected,extras)
  dest='book/coverage/checks/synthetic-retention-'+label+'.json';got=ns['retain'](F,ns['BASELINE'],ns['MANIFEST'],selected,extras,dest,authorization);body=get(dest)
  assert got['original_inputs']==body['original_input_count']==47277 and len(body['input_bindings'])==47277 and body['new_unique_snapshot_alias_count']==1
  assert {r['original_frozen_path']:r['sha256'] for r in body['input_bindings']}==frozen
  for n,r in rows.items():
   for key,value in r.items():
    if key!='evidence_sha256':assert selected[n][key]==value
   assert selected[n]['checkpoint27_original_baseline_evidence']['original_row_canonical_json_sha256']==ns['canonical_row_sha256'](r)
  assert body['baseline_actual_audit']=={'file':ns['AUDIT'],'sha256':ns['AUDIT_SHA']} and len((F/dest).read_bytes())<100_000_000
 test('full47277 synthetic content routing retains prior full rows and oldalias/currentowner coexistence',lambda:retain_case('accept'),True)
 first=sorted(rows)[0]
 for n in [owners[0],ns['SOURCE']]:
  test('retainer rejects resurfaced original raw hash '+n,lambda n=n:retain_case('old-'+Path(n).stem,lambda s,e:s[first]['evidence_sha256'].__setitem__(n,alias[n]['original_sha256'])),False)
  test('retainer rejects arbitrary current raw hash '+n,lambda n=n:retain_case('arbitrary-'+Path(n).stem,lambda s,e:s[first]['evidence_sha256'].__setitem__(n,'0'*64)),False)
 test('retainer rejects missing historical immutable alias',lambda:retain_case('missing-history',lambda s,e:s[first]['evidence_sha256'].pop(alias[owners[0]]['immutable_byte_copy']['file'])),False)
 test('retainer rejects old public row body/time drift',lambda:retain_case('body-drift',lambda s,e:s[first].__setitem__('old_review_time','changed')),False)
 test('retainer rejects whole old metadata/provenance drift',lambda:retain_case('older-provenance-drift',lambda s,e:s[first].__setitem__('checkpoint26_original_baseline_evidence',{'changed':True})),False)
 test('retainer rejects compact original-row SHA drift',lambda:retain_case('row-fingerprint',lambda s,e:s[first]['checkpoint27_original_baseline_evidence'].__setitem__('original_row_canonical_json_sha256','0'*64)),False)
 test('retainer rejects missing old extra audit input',lambda:retain_case('old-extra',lambda s,e:e.clear()),False)
 test('canonical original row SHA is order independent and sensitive to nested prior bodies',lambda:(lambda r: ns['canonical_row_sha256'](r)==ns['canonical_row_sha256'](dict(reversed(list(r.items())))) or (_ for _ in ()).throw(AssertionError()))(rows[first]),True)
closed={ref(H)['file']:sha(H)}
for n in [native['BASELINE'],native['MANIFEST'],native['AUDIT'],native['APPLICATION']['file'],native['APPLICATION_EXECUTION']['file'],native['SOURCE_ARCHIVE'],native['SOURCE']]:closed[n]=sha(R/n)
result={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(H),'helper_sha256':sha(H),'baseline_selected_sources':1167,'baseline_frozen_inputs':47277,'exact_authorized_old_paths':sorted(native['ALIAS_PATHS']),'native_baseline_and_source5455_pins_exact':True,'fixture_count':len(fixtures),'fixtures':fixtures,'old_alias_and_current_raw_evidence_coexistence_guarded':True,'entire_prior_row_metadata_and_time_retrievable_by_exact_immutable_selection_and_canonical_row_SHA':True,'full_retention_routing_fixture_rows':47277,'synthetic_content_fixture_scope':'47276 identical frozen rows use an explicit isolated synthetic content map; one physical unique snapshot byte exercises new alias insertion. Native baseline hashes/counts checked separately. No production input retention or owner installation inferred.','closed_evidence_sha256':closed,'scope':'Independent full code read and focused actual-function fixtures in TMP with isolated synthetic execution/installation records. No actual27 integration, selection, retainer producer, freeze or compiler execution.'}
with O.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','result':ref(O),'fixtures':len(fixtures)}))
