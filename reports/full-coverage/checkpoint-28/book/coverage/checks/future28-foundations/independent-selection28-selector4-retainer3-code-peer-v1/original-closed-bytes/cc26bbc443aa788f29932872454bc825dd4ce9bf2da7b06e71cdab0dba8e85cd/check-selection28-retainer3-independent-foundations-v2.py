from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,sys,tempfile,time
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/selection28-retainer3-independent-foundations-findings-v2.json')
S=R/'book/coverage/prepare_checkpoint28_selection_v3.py';T=R/'book/coverage/retain_baseline_inputs28_v3.py';N=R/'book/coverage/lean_names.py'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_bytes())
def ref(p):return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':h(p)}
assert h(S)=='8ea67aa15c3c11335fc040ba9132aa65761c47f21459083567955ef745ae9a87'and h(T)=='e3014dd7e7951d74b7c87f082f0d7395825bc3d61b90e630709f71794dbc23e8'and h(N)=='9e00c114c57a2bb05939a21bee09679188aa97c855a8d10e61b160f31e10f07d'and not OUT.exists()
start=datetime.now(timezone.utc).isoformat();sys.path.insert(0,str(R/'book/coverage'))
def load(name,p):
 spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
m=load('selection28_exact3_independent',S);t=load('retainer28_exact3_independent',T)
obs=[]
def reject(name,fn):
 try:fn()
 except (AssertionError,ValueError,KeyError,TypeError):obs.append({'fixture':name,'rejected':True});return
 raise AssertionError('Expected rejection: '+name)
cmd=['lake','env','lean','SafeLearning/Example.lean'];cwd=str(R/'verification/lean')
good={'exit_code':0,'actual_exit_code':0,'actual_runner_exit_code':0,'actual_command':cmd,'command':cmd,'actual_workdir':cwd,'working_directory':cwd,'workdir':cwd,'cwd':cwd,'status':'passed'}
m.native_record(good,cmd,cwd);obs.append({'fixture':'all_present_native_aliases_consistent_exact_integer_zero','passed':True})
for key in ('actual_exit_code','exit_code','actual_runner_exit_code'):
 for value in (False,True,1,'0',None):
  bad=dict(good);bad[key]=value;reject('native_'+key+'_rejects_'+repr(value),lambda bad=bad:m.native_record(bad,cmd,cwd))
reject('native_missing_all_exit_aliases',lambda:m.native_record({k:v for k,v in good.items()if k not in ('actual_exit_code','exit_code','actual_runner_exit_code')},cmd,cwd))
for key in ('actual_command','command'):
 bad=dict(good);bad[key]=['false'];reject('native_conflicting_'+key,lambda bad=bad:m.native_record(bad,cmd,cwd))
reject('native_missing_command',lambda:m.native_record({k:v for k,v in good.items()if k not in ('actual_command','command')},cmd,cwd))
for key in ('actual_workdir','working_directory','workdir','cwd'):
 bad=dict(good);bad[key]='/tmp/conflicting';reject('native_conflicting_'+key,lambda bad=bad:m.native_record(bad,cmd,cwd))
reject('native_missing_directory',lambda:m.native_record({k:v for k,v in good.items()if k not in ('actual_workdir','working_directory','workdir','cwd')},cmd,cwd))
for value in ('failed',None,False):
 bad=dict(good);bad['status']=value;reject('native_bad_status_'+repr(value),lambda bad=bad:m.native_record(bad,cmd,cwd))
audit=j(R/t.AUDIT);assert len(audit['checks'])==1178
for p,namespace in [(S,m.__dict__),(T,{})]:
 tree=ast.parse(p.read_text());loops=[x for x in ast.walk(tree)if isinstance(x,ast.For)and ast.unparse(x.iter)=="audit['checks']"]
 assert len(loops)==1;code=compile(ast.fix_missing_locations(ast.Module(body=loops,type_ignores=[])),str(p)+':exact-audit-loop','exec')
 exec(code,dict(namespace,audit=audit));obs.append({'fixture':'actual1178_native_audit_checks_exact_loop_'+p.name,'passed':True})
 for k,v in [('actual_exit_code',1),('actual_runner_exit_code',False),('actual_command',['false']),('cwd','/tmp/a'),('working_directory','/tmp/b'),('status','failed')]:
  bad=copy.deepcopy(audit);bad['checks'][0][k]=v
  if k in ('cwd','working_directory'):bad['checks'][0]['actual_workdir']=str(R/'verification/lean')
  reject('actual_native_audit_loop_'+p.name+'_conflicting_'+k,lambda bad=bad:exec(code,dict(namespace,audit=bad)))
ready=j(R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json');ready2=j(R/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json')
all_pairs=ready['actual_paired_records']+ready2['actual_paired_records'];newrows=ready['sources']+ready2['sources'];assert len(newrows)==11 and len(all_pairs)==22
foundation=j(R/'book/coverage/checks/future28-foundations/current60-owner28-v1/foundations28-current60-final-offer-v1.json')
pair=[p for p in all_pairs if p['source']['file']==next(iter(foundation['proof_files']))]
proof=foundation['proof_files'][pair[0]['source']['file']]
e=m.proof_evidence(proof,pair,foundation['required_evidence_artifacts_sha256']);assert all(e[r['file']]==r['sha256']for p in pair for r in [p[k]for k in ('actual_record','raw_log','source_snapshot')])
obs.append({'fixture':'actual_foundation_dictionary_proof_evidence_complete_pair','passed':True})
pair=[p for p in all_pairs if 'CompleteModulesSensorCommissioning28.lean' in p['source']['file']]
closure={p[k]['file']:p[k]['sha256']for p in pair for k in ('actual_record','raw_log','source_snapshot')};stringproof={'evidence_sha256':next(p['actual_record']['sha256']for p in pair if p['kind']=='standalone')}
assert m.proof_evidence(stringproof,pair,closure)==closure;obs.append({'fixture':'actual_module_native_standalone_string_derives_complete_six_pair_refs','passed':True})
for value in (False,'0'*64,0,[]):reject('proof_evidence_wrong_native_variant_'+repr(value),lambda value=value:m.proof_evidence({'evidence_sha256':value},pair,closure))
missing=dict(closure);missing.pop(pair[0]['raw_log']['file']);reject('proof_evidence_missing_pair_closure',lambda:m.proof_evidence(stringproof,pair,missing))
conflict={'evidence_sha256':{pair[0]['raw_log']['file']:'0'*64}};reject('proof_evidence_conflicting_pair_hash',lambda:m.proof_evidence(conflict,pair,closure))
badpair=copy.deepcopy(pair);badpair[0]['actual_record']['unexpected']=True;reject('proof_evidence_extra_ref_field',lambda:m.proof_evidence(stringproof,badpair,closure))
for name in ('/tmp/escape','../escape','book/../escape'):
 reject('unsafe_root_path_'+name,lambda name=name:m.safe(name))
reject('merge_hash_conflict',lambda:m.merge({'a':'0'*64},{'a':'1'*64}))
reject('checked_native_wrong_sha',lambda:m.checked({'file':'book/coverage/lean_names.py','sha256':'0'*64}))
reject('checked_native_extra_ref_field',lambda:m.checked({'file':'book/coverage/lean_names.py','sha256':h(N),'unexpected':True}))
parser=m.declarations
sample='namespace Outer\n/- theorem fake : True := by trivial /- nested -/ -/\nprivate theorem hidden : True := by trivial\nsection inner\n@[simp] theorem shown : True := by trivial\nend inner\nnamespace Child\ndef real := 1\nend Child\nend Outer\n'
assert parser(sample)==[{'name':'Outer.shown','kind':'theorem'},{'name':'Outer.Child.real','kind':'def'}];obs.append({'fixture':'exact_parser_nested_comments_private_attributes_sections_namespace','passed':True})
for label,text in [('unclosed_comment','namespace A\n/-'),('unclosed_string','namespace A\n#check "'),('unclosed_attribute','namespace A\n@[simp\ntheorem x'),('duplicate','namespace A\ntheorem x\ntheorem x\nend A'),('wrong_scope','namespace A\nend B'),('missing_scope','theorem x'),('unclosed_namespace','namespace A\ntheorem x')]:reject('parser_'+label,lambda text=text:parser(text))
baseline=j(R/t.BASELINE);manifest=j(R/t.MANIFEST)
assert len(baseline['proof_files'])==1175 and len(manifest['frozen_inputs_sha256'])==48662
for label,change in [('missing_old_source',lambda s,e:s.pop(next(iter(s)))),('changed_old_row_field',lambda s,e:s[next(iter(s))].__setitem__('evidence_scope','changed fixture value')),('wrong_old_source_sha',lambda s,e:s[next(iter(s))].__setitem__('sha256','0'*64)),('missing_old_extra',lambda s,e:e.pop(next(iter(e))))]:
 selected=copy.deepcopy(baseline['proof_files']);extras=copy.deepcopy(baseline['extra_frozen_inputs']);change(selected,extras)
 reject('real_retainer_'+label,lambda:t.retain(R,selected,extras,'book/coverage/checks/future28-foundations/selection28-code-review-unwritten-negative-content-map-v2.json'))
dest='book/coverage/checks/future28-foundations/selection28-code-review-unwritten-content-map-v1.json'
selected=copy.deepcopy(baseline['proof_files']);extras=copy.deepcopy(baseline['extra_frozen_inputs']);assert not(R/dest).exists()
print('Beginning genuine pure retention of1175 original full rows and48662 frozen inputs.',flush=True)
tm=time.monotonic();retained=t.retain(R,selected,extras,dest);duration=time.monotonic()-tm
assert not(R/dest).exists();payload=retained['payload'];data=json.loads(payload)
assert len(data['input_bindings'])==48662 and {x['original_frozen_path']:x['sha256']for x in data['input_bindings']}==manifest['frozen_inputs_sha256']
assert hashlib.sha256(payload).hexdigest()==retained['provenance']['sha256']and len(payload)<100_000_000
for n,old in baseline['proof_files'].items():
 current=selected[n]
 for k,v in old.items():
  if k=='evidence_sha256':assert all(current[k].get(p)==s for p,s in v.items())
  else:assert current[k]==v,(n,k)
assert all(extras[n]==v for n,v in baseline['extra_frozen_inputs'].items())
obs.append({'fixture':'genuine_unmodified_retainer_complete1175_rows48662_frozen_inputs_no_filesystem_output','passed':True})
all_sources={n:r['sha256']for n,r in baseline['proof_files'].items()}
all_sources.update({x['canonical_source']:x['original_tmp_source']['sha256']for x in newrows});assert len(all_sources)==1186
names=[];theorems=[]
for n,s in all_sources.items():
 assert h(R/n)==s,n;decl=parser((R/n).read_text());names.extend(x['name']for x in decl);theorems.extend(x['name']for x in decl if x['kind']in ('theorem','lemma'))
assert len(names)==len(set(names))and len(theorems)==len(set(theorems))==9896
assert sum(len([x for x in parser((R/r['canonical_source']).read_text())if x['kind']in ('theorem','lemma')])for r in newrows)==252
obs.append({'fixture':'actual1186_source_hashes_and_unique9896_theorem252_new_names','passed':True})
# The genuine full production plan remains unavailable; these assertions certify
# source control flow, not a substituted positive execution of prepare().
tree=ast.parse(S.read_text());prepare=next(x for x in tree.body if isinstance(x,ast.FunctionDef)and x.name=='prepare')
readonly=next(x for x in prepare.body if isinstance(x,ast.If)and ast.unparse(x.test)=='not apply')
retaincall=next(x for x in prepare.body if isinstance(x,ast.Assign)and isinstance(x.value,ast.Call)and ast.unparse(x.value.func)=='retain')
assert retaincall.lineno<readonly.lineno
assert all(x.lineno<readonly.lineno for x in prepare.body if isinstance(x,ast.Assert)and ('len(payload)'in ast.unparse(x.test)or 'len(retained' in ast.unparse(x.test)))
assert all(x.lineno>readonly.lineno for x in ast.walk(prepare)if isinstance(x,ast.Call)and isinstance(x.func,ast.Attribute)and x.func.attr in ('open','mkdir','write'))
assert not any(isinstance(x,ast.Call)and isinstance(x.func,ast.Attribute)and x.func.attr in ('open','mkdir','write','write_bytes','write_text')for x in ast.walk(ast.parse(T.read_text())))
obs.append({'fixture':'full_readonly_control_flow_after_both_payload_sizes_paths_source_sha_pure_retainer_no_write_methods','passed_static_flow_check':True})
out={'original_reader1_interrupted_for_own_masked_negative_fixture':{'file':'/tmp/selection28-retainer3-independent-foundations-actual-v1.json','sha256':'6461f606306991b7a47d6adfac669cdac39f3af092c8b443e205de7df923bfbc','actual_exit_code':-15,'reason':'Own reader fixture added absent theorem_count and invalid destination masked rejection; interrupted prior to final findings, unchanged producer has no detected defect.'},'status':'passed_full_independent_selection28_retainer3_code_native_guards_and_complete_pure_baseline_retention_review','errors':[],'reviewer':'/root/foundations_recovery28','reader_started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(S),'retainer':ref(T),'parser_dependency':ref(N),'reviewed_helpers_sha256':{str(p.relative_to(R)):h(p)for p in [S,T,N]},'full_source_lines_read':{str(p.relative_to(R)):len(p.read_text().splitlines())for p in [S,T,N]},'fixture_count':len(obs),'fixture_observations':obs,'genuine_complete_baseline_retainer':{'actual_unmodified_function':'retain_baseline_inputs28_v3.retain','original_sources':1175,'original_frozen_inputs':48662,'original_full_rows_and_fields_preserved':True,'original_extra_frozen_rows_preserved':True,'content_map_prepared_bytes':len(payload),'content_map_payload_sha256':hashlib.sha256(payload).hexdigest(),'retained_existing_content_rows':data['retained_existing_content_rows'],'new_unique_snapshot_alias_count':data['new_unique_snapshot_alias_count'],'new_unique_snapshot_alias_bytes':data['new_unique_snapshot_alias_bytes'],'elapsed_seconds':duration,'production_or_review_contentmap_written':False},'actual_source_name_index':{'source_count':1186,'public_theorem_lemma_names':9896,'new_sources':11,'new_public_theorem_lemma_names':252,'source_sha_checked':True,'kernel_compilation_or_axiom_check_claimed_by_source_index':False},'complete_genuine_production_selection_plan_preflight_executed':False,'fresh_actual_plan_preflight_pending_root_owner28_integration_and_global_integrity':True,'production_selector_writer_executed':False,'coverage_complete':False,'scope':'Full exact code and independent meaningful pure/native-schema fixtures, plus genuine unmodified complete baseline retention performed without output writes. Actual production plan is not yet available; a fresh unmodified prepare(False) is still required before Root execution.'}
with OUT.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'findings':ref(OUT),'fixture_count':len(obs),'genuine_retained_original_inputs':48662,'pure_retention_seconds':duration,'production_plan_preflight_pending':True}))
