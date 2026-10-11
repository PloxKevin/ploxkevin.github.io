from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-core'
OLD=ROOT/'book/coverage/checks/root_integrate_owner24_candidates_v2.py';NEW=ROOT/'book/coverage/checks/root_integrate_owner24_candidates_v3.py'
OUT=BASE/'owner24-integration-helper-independent-foundations-code-review-v2.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
ref=lambda p:{'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
assert not OUT.exists() and H(OLD)=='07980ea65f4f983e832d761579e68fa0000c362aa8a8ffb9c2b8800bf6dd2489' and H(NEW)=='57df986e038a2867b8a4c0b3247abbfaa8845bcaa9db52a69074dea8776250ef'
priorp=BASE/'owner24-integration-helper-independent-foundations-code-review-v1.json';prior=read(priorp)
assert H(priorp)=='6251411a9ce6bf439f094c5c9b790577a093f570ea60006a6cb63278b5bde2c6' and 'passed' in prior['status'] and prior['errors']==[]
told,tnew=[ast.parse(p.read_text()) for p in [OLD,NEW]]
def pair(tree):
 o=next(n for n in tree.body if isinstance(n,ast.For) and ast.unparse(n.target)=='owner')
 p=next(n for n in o.body if isinstance(n,ast.For) and ast.unparse(n.target)=='(name, proof)')
 return next(n for n in p.body if isinstance(n,ast.For) and ast.unparse(n.target)=='ref')
a,b=pair(told),pair(tnew)
i=next(i for i,n in enumerate(a.body) if isinstance(n,ast.Assert) and "execution['log_sha256']" in ast.unparse(n))
j=next(i for i,n in enumerate(b.body) if isinstance(n,ast.Assign) and ast.unparse(n.targets[0])=='log_digests')
assert i==j
normalized=copy.deepcopy(told);pair(normalized).body[i:i+1]=copy.deepcopy(b.body[j:j+3]);assert ast.dump(normalized)==ast.dump(tnew)
offers={
 'core':'book/coverage/checks/future24-core/core-audit24-candidate-source51-material-additions-v1-reviewed.json',
 'foundations':'book/coverage/checks/foundations-future24/source51/foundations-audit24-candidate-source51-additions-v1-reviewed.json',
 'applied':'book/coverage/checks/applied-future24/source51/applied-audit24-candidate-source51-additions-v2-reviewed.json',
 'modules':'book/coverage/checks/modules-future24/source51/modules-audit24-candidate-source51-additions-v1-reviewed.json'}
native=[];counts={};fixtures=[]
def run_pair(recordp,name,proof,mutator=None,reference_delta=None):
 original=read(recordp);r=copy.deepcopy(original)
 command=original.get('actual_command',original.get('command'))
 logname=original.get('log',original.get('raw_log'));logsha=original.get('log_sha256',original.get('raw_log_sha256'))
 assert H(ROOT/name)==original['source_sha256_before']==original['source_sha256_after']==proof['sha256']
 reference=dict(ref(recordp),actual_source=name,actual_command=command,actual_workdir=original['actual_workdir'],canonical_raw_log={'file':logname,'sha256':logsha})
 assert H(ROOT/logname)==logsha
 if mutator:mutator(r)
 if reference_delta:reference_delta(reference)
 env={'ROOT':ROOT,'reference':lambda _:r,'sha':lambda n:H(ROOT/n),'name':name,'proof':proof,'ref':reference,'retained_reference_sha256':{}}
 exec(compile(ast.Module(body=b.body,type_ignores=[]),str(NEW),'exec'),env)
 return original,reference
for owner,offerpath in offers.items():
 offer=read(ROOT/offerpath);counts[owner]=0
 for name,proof in offer['proof_files'].items():
  selected=[]
  if 'actual_paired_records' in proof:selected=[r['actual_record'] for r in proof['actual_paired_records']]
  elif 'standalone_evidence' in proof:selected=[{'file':proof[k],'sha256':proof[k+'_sha256']} for k in ['standalone_evidence','named_evidence']]
  else:
   for n,h in proof['evidence_sha256'].items():
    if n.endswith('.json'):
     z=read(ROOT/n)
     if z.get('source')==name and any(k in z for k in ['actual_exit_code','exit_code']):selected.append({'file':n,'sha256':h})
  assert len(selected)==2,(owner,name,selected)
  for rr in selected:
   p=ROOT/rr['file'];assert H(p)==rr['sha256']
   original,reference=run_pair(p,name,proof)
   native.append({'owner':owner,'source':name,'proof_sha256':proof['sha256'],'record':ref(p),'entire_original_record_body_and_time':original,'canonical_raw_log':reference['canonical_raw_log']})
   counts[owner]+=1
assert counts=={'core':2,'foundations':10,'applied':8,'modules':6} and len(native)==26
fixtures.append('accept_all26_real_native_paired_records_across13_new_immutable_sources')
module=next(r for r in native if r['owner']=='modules');p=ROOT/module['record']['file'];proof={'sha256':module['proof_sha256']};name=module['source']
assert 'raw_log_sha256' in module['entire_original_record_body_and_time'] and 'log_sha256' not in module['entire_original_record_body_and_time']
run_pair(p,name,proof,lambda x:x.update(log_sha256=x['raw_log_sha256']));fixtures.append('accept_equal_raw_log_sha256_and_log_sha256_aliases')
run_pair(p,name,proof,lambda x:x.update(log_sha256=x.pop('raw_log_sha256')));fixtures.append('accept_sole_log_sha256_schema')
def reject(label,mutation=None,refmutation=None):
 try:run_pair(p,name,proof,mutation,refmutation)
 except AssertionError:fixtures.append('reject_'+label)
 else:raise AssertionError(label+' accepted')
reject('conflicting_raw_and_log_digest_fields',lambda x:x.update(log_sha256='0'*64))
reject('sole_wrong_raw_log_digest',lambda x:x.update(raw_log_sha256='0'*64))
reject('no_log_digest_field',lambda x:x.pop('raw_log_sha256'))
reject('canonical_log_digest_changed',refmutation=lambda x:x['canonical_raw_log'].update(sha256='0'*64))
reject('canonical_log_path_with_different_actual_bytes',refmutation=lambda x:x['canonical_raw_log'].update(file='book/coverage/foundations.json'))
reject('conflicting_command_alias',lambda x:x.update(command=['false']))
reject('conflicting_exit_alias',lambda x:x.update(exit_code=1))
reject('actual_source_after_changed',lambda x:x.update(source_sha256_after='0'*64))
report={'status':'passed_independent_owner24_integration_helper_v3_native26_pair_schema_and_exact_log_alias_delta',
 'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(NEW),'helper_sha256':H(NEW),'checker':ref(Path(__file__)),
 'previous_review':ref(priorp),'entire_original_v2_code_review_body_and_time':prior,'original_unexecuted_v2_helper':ref(OLD),
 'v2_to_v3_only_exact_raw_log_sha256_or_log_sha256_alias_validation_delta':True,
 'actual_native_paired_records_by_owner':counts,'actual_all26_native_records_and_canonical_raw_logs':native,
 'original_source51_final_offer_references':{owner:ref(ROOT/p) for owner,p in offers.items()},
 'explicit_focused_accept_reject_fixtures':fixtures,'all_other_preconditions_copy_scope_and_before_after_guards_unchanged':True,
 'Root_integration_main_dry_apply_executed':False,'final_all_four_source52_bindings_reviewed_or_released':False,'errors':[],
 'scope':'Narrow helper code delta and real native paired-record schema checks. All13 existing unselected source pairs26 actual0 records/raw logs were read directly and remain unchanged. No compiler rerun or synthetic actual execution. Prior v2 review covered Foundation log_sha256 records; this genuine additional code/schema peer closes the Module raw_log_sha256 field. Root actual source52 completion/final identity candidates/peers/binding/dry/apply still required.'}
with OUT.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'review':ref(OUT),'helper_sha256':H(NEW),'actual_native_records':counts,'fixtures':len(fixtures),'integration_executed':False}))
