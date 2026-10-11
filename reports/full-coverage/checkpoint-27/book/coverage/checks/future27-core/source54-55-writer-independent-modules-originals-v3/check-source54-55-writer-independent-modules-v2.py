from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER=ROOT/'book/coverage/checks/root_apply_source54_55_v3.py'
OLD=ROOT/'book/coverage/checks/root_apply_source54_55_v1.py'
OUT=Path('/tmp/source54-55-writer-independent-modules-code-review-v3.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def ref(p):return {'file':str(p),'sha256':sha(p)}
assert sha(HELPER)=='6b4c52ce05d8ed940a22982107b2ba708dc0f6f28e1a60ab4396b78c68286be0'
text=HELPER.read_text();ast.parse(text)
old=OLD.read_text()
V2=ROOT/'book/coverage/checks/root_apply_source54_55_v2.py'
oldblock="""    originals={}
    for n,h in evidence.items():
        p=Path(n) if Path(n).is_absolute() else safe(n)
"""
newblock="""    originals={}
    exact_external_aliases={}
    external_name='verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean'
    external_hash='e430f9176d3609cf18d6ae4abdd94a8bd6d30018734a7605b26de369968358ac'
    external_alias_name='book/coverage/checks/future27-core/source54-exact-mathlib-matrix-norm-original-v1.lean'
    for n,h in evidence.items():
        if n==external_name:
            assert h==external_hash and sha(ROOT/n)==h
            p=safe(external_alias_name);assert sha(p)==h
            exact_external_aliases[str(ROOT/n)]=str(p)
        else:
            p=Path(n) if Path(n).is_absolute() else safe(n)
"""
assert text.count(newblock)==1
v2=text.replace(newblock,oldblock).replace("    for original_name,canonical_name in exact_external_aliases.items():\n        assert original_name not in aliases and canonical_name in aliases\n        aliases[original_name]=aliases[canonical_name]\n",'').replace("        'original_absolute_byte_aliases':aliases,'exact_original_external_source_aliases':exact_external_aliases,\n        'entire_original_proposal_bodies_and_times':proposals,\n","        'original_absolute_byte_aliases':aliases,'entire_original_proposal_bodies_and_times':proposals,\n")
assert v2==V2.read_text()
normalized=v2.replace('closed-checkpoint26-delivery-originals-v2/','closed-checkpoint26-delivery-originals-v1/').replace("    for table in [q54['evidence_sha256'],q55['closed_evidence_sha256']]:\n        for n,h in table.items():\n            assert n not in evidence or evidence[n]==h,n\n            evidence[n]=h\n","    evidence.update(q54['evidence_sha256']);evidence.update(q55['closed_evidence_sha256'])\n")
assert normalized==old
spec=importlib.util.spec_from_file_location('independent_source54_55_writer',HELPER)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
sys.path.insert(0,str(ROOT/'book'))
manifest=read(ROOT/'reports/full-coverage/checkpoint-26-manifest.json')
protected={n:r['sha256'] for n,r in manifest['proof_files'].items()}
protected.update({n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in {'book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules','applied-promotions']}})
for p in [HELPER,OLD,V2,m.CONTRACT,ROOT/'book/coverage/inventory.json',ROOT/'book/coverage/material-corrections.json',ROOT/'book/coverage/inventory-after-correction53.json',ROOT/'book/inventory_claims.py']:
 protected[str(p)]=sha(p)
for n,h in protected.items():assert sha(Path(n) if Path(n).is_absolute() else ROOT/n)==h,n
absent=[m.OUT,m.HISTORY,*[ROOT/f'book/coverage/inventory-{side}-correction{num}.json' for side in ['before','after'] for num in [54,55]]]
assert all(not p.exists() for p in absent)
parsed=[];original_parser=m.full_parser

def collect(candidates):
 data,d=original_parser(candidates);parsed.append((data,d,copy.deepcopy(candidates)));return data,d
m.full_parser=collect
class BeforeFirstWrite(Exception):pass
attempt=[]
def stop_write(p,data):
 attempt.append({'file':str(p),'data_sha256':hashlib.sha256(data).hexdigest()});raise BeforeFirstWrite
m.write_new=stop_write
try:m.main()
except BeforeFirstWrite:pass
else:raise AssertionError('native prewrite did not reach controlled first-write boundary')
assert len(attempt)==1 and attempt[0]['file']==str(m.HISTORY/'source53-original-root/book/coverage/inventory.json')
assert len(parsed)==2
contract=read(m.CONTRACT)
assert contract['steps'][0]['exact_changed_text_keys']=={'exercises':[],'material_source_units':['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739']}
assert contract['steps'][1]['exact_changed_text_keys']=={'exercises':['verification.html::exercise-17'],'material_source_units':['verification.html::node-1184']}
assert len(parsed[0][1]['source_sha256'])==len(parsed[1][1]['source_sha256'])==29
assert parsed[1][1]['source_sha256']==contract['final_page_sources_sha256']
fixtures=[]
def fixture(name,f,accept=False):
 try:f()
 except (AssertionError,KeyError,ValueError,TypeError):
  assert not accept,name;fixtures.append({'name':name,'expected':'reject','observed':'rejected'});return
 assert accept,name;fixtures.append({'name':name,'expected':'accept','observed':'accepted'})
fixture('canonical relative path',lambda:m.safe('book/coverage/inventory.json'),True)
for name in ['', '../book/coverage/inventory.json','/tmp/x','book//coverage/x','book/./coverage/x','book/coverage/x\n','book/coverage/x\r','book/coverage/x\0']:
 fixture('unsafe path '+repr(name),lambda name=name:m.safe(name))
orig_read=m.read;orig_sha=m.sha

def fake_actual(row):
 m.read=lambda _:row;m.sha=lambda _:'a'*64
 try:return m.actual('explicit_in_memory_fixture')
 finally:m.read=orig_read;m.sha=orig_sha
base={'actual_exit_code':0,'exit_code':0,'log':'reports/full-coverage/fixture.log','log_sha256':'a'*64}
fixture('two genuine integer zero exits',lambda:fake_actual(base),True)
fixture('single genuine integer zero exit',lambda:fake_actual({k:v for k,v in base.items() if k!='exit_code'}),True)
for name,changes,remove in [('bool actual',{'actual_exit_code':False},[]),('bool exit',{'exit_code':False},[]),('float zero',{'actual_exit_code':0.0},[]),('string zero',{'actual_exit_code':'0'},[]),('nonzero',{'exit_code':1},[]),('missing both',{},['actual_exit_code','exit_code']),('wrong log digest',{'log_sha256':'b'*64},[]),('unsafe absolute log',{'log':'/tmp/fixture'},[])]:
 row={k:v for k,v in base.items() if k not in remove};row.update(changes);fixture(name,lambda row=row:fake_actual(row))
previous=read(ROOT/'book/coverage/inventory.json')
for index,(data,after,candidates) in enumerate(parsed):
 step=contract['steps'][index]
 fixture('native full29 step '+str(step['correction_id']),lambda previous=previous,after=after,step=step:m.inventory_diff(previous,after,step),True)
 mutations=[]
 x=copy.deepcopy(after);x['counts']['exercises']+=1;mutations.append(('counts drift',x,step))
 x=copy.deepcopy(after);x['source_sha256'][next(n for n in x['source_sha256'] if n!=step['source'])]='0'*64;mutations.append(('unrelated source identity drift',x,step))
 x=copy.deepcopy(after);x['exercises'][0]['key']='foreign-key';mutations.append(('exercise key drift',x,step))
 x=copy.deepcopy(after);x['material_source_units'][0]['line']+=1;mutations.append(('literal line drift',x,step))
 x=copy.deepcopy(after);key=next(r for r in x['material_source_units'] if r['source']!=step['source']);key['source_text']+=' foreign';mutations.append(('unrelated literal body drift',x,step))
 wrong=copy.deepcopy(step);wrong['exact_changed_text_keys']['material_source_units']=[];mutations.append(('missing changed-unit authorization',after,wrong))
 for name,x,s in mutations:fixture(str(step['correction_id'])+' '+name,lambda previous=previous,x=x,s=s:m.inventory_diff(previous,x,s))
 previous=after
# The actual archive mapping is injective, even after the explicitly documented .txt->.txt.log normalization.
evidence={str(m.CONTRACT):m.CONTRACT_SHA}
for p,h,q,qh in zip(m.PROPOSALS,m.PROPOSAL_SHAS,m.PEERS,m.PEER_SHAS):evidence[str(p)]=h;evidence[str(q)]=qh
q54,q55=[read(p) for p in m.PEERS]
for table in [q54['evidence_sha256'],q55['closed_evidence_sha256']]:
 for n,h in table.items():assert n not in evidence or evidence[n]==h;evidence[n]=h
# Execute the exact new archive-input validator block in isolated accept/reject fixtures.
validator=text[text.index('    originals={}'):text.index("    originals[str(Path('/tmp/root_prepare_source54_55_parser_contract27_v1.py'))]")]
import textwrap
validator=textwrap.dedent(validator)
external='verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean'
hash_external='e430f9176d3609cf18d6ae4abdd94a8bd6d30018734a7605b26de369968358ac'
canonical='book/coverage/checks/future27-core/source54-exact-mathlib-matrix-norm-original-v1.lean'
def archive_validate(table,sha_override=None):
 env={'Path':Path,'ROOT':ROOT,'safe':m.safe,'sha':sha_override or m.sha,'evidence':table}
 exec(compile(validator,'<exact_writer3_archive_validator>','exec'),env)
 return env
fixture('exact one external Mathlib path/hash accepted through byte-identical canonical alias',lambda:archive_validate({external:hash_external}),True)
fixture('external original hash drift rejected',lambda:archive_validate({external:'0'*64}))
fixture('external actual bytes drift rejected',lambda:archive_validate({external:hash_external},lambda p:'0'*64 if p==ROOT/external else sha(p)))
fixture('canonical byte-alias drift rejected',lambda:archive_validate({external:hash_external},lambda p:'0'*64 if p==ROOT/canonical else sha(p)))
fixture('other external-resolved Mathlib path rejected',lambda:archive_validate({'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean':'0'*64}))
validated=archive_validate(evidence);originals=validated['originals'];assert validated['exact_external_aliases']=={str(ROOT/external):str(ROOT/canonical)}
for p in [Path('/tmp/root_prepare_source54_55_parser_contract27_v1.py'),Path('/tmp/root_prepare_source54_55_parser_contract27_v2.py')]:originals[str(p)]=sha(p)
destinations={}
for n,h in originals.items():
 p=Path(n);target=m.HISTORY/('semantic-original-root' if p.is_relative_to(ROOT) else 'semantic-original-tmp')/(p.relative_to(ROOT) if p.is_relative_to(ROOT) else p.name)
 if target.suffix=='.txt':target=target.with_suffix('.txt.log')
 assert str(target) not in destinations,(n,destinations.get(str(target)))
 destinations[str(target)]=n;assert sha(p)==h
for n,h in protected.items():assert sha(Path(n) if Path(n).is_absolute() else ROOT/n)==h,n
assert all(not p.exists() for p in absent)
closer=ROOT/'book/coverage/checks/future27-core/closed-checkpoint26-delivery-originals-v2/closed-original-byte-aliases-v1.json'
closed={str(HELPER):sha(HELPER),str(OLD):sha(OLD),str(V2):sha(V2),str(m.CONTRACT):sha(m.CONTRACT),str(closer):sha(closer),str(ROOT/'book/inventory_claims.py'):sha(ROOT/'book/inventory_claims.py'),str(Path(__file__)):sha(Path(__file__))}
for n,h in originals.items():assert n not in closed or closed[n]==h;closed[n]=h
historyfiles=[Path('/tmp/check-source54-55-writer-independent-modules-v1.py'),Path('/tmp/run-source54-55-writer-independent-modules-actual-v1.py'),Path('/tmp/source54-55-writer-independent-modules-actual-v1.json'),Path('/tmp/source54-55-writer-independent-modules-actual-v1.log'),Path('/tmp/root-source54-55-planning-reader1-native-tool-result-observation-v1.json'),ROOT/'book/coverage/checks/future27-core/source54-exact-mathlib-matrix-norm-original-v1.byte-alias.json']
for p in historyfiles:closed[str(p)]=sha(p)
assert read(historyfiles[2])['actual_exit_code']==1
assert sha(historyfiles[4])=='2552c34cc86466af2a7c98e2e1ad4b4b8ca1a339504d3ebbc40a1f89e51e52c8'
result={'status':'passed_full_code_delta_native_prewrite_and_focused_reject_fixtures_no_application','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent Modules agent','helper':ref(HELPER),'helper_sha256':sha(HELPER),'original_unexecuted_writer1':ref(OLD),'errors':[],
 'entire_final_writer_source':text, 'whole_code_review':{'entire_final_helper_read':True,'exact_v1_to_v2_delta':['actual completed-delivery closer-v2 path','reject conflicting semantic evidence hashes instead of silent overwrite'],'exact_v2_to_v3_delta':['sole pinned Normed.lean original path/hash resolves through an exact byte-identical canonical alias','history preserves both original external path and canonical alias without rewriting original reviews'],'strict_int_zero_wrapper_exits':True,'all_guards_precede_first_write':True,'source_reconstruction_reverse_bytes_and_DOM':True,'both_full29_parsers_run':True,'all_original_semantic_review_bodies_and_times_preserved':True,'archive_destinations_unique':len(destinations)},
 'native_prewrite':{'status':'passed_to_first_archive_write_with_write_new_replaced_by_nonwriting_sentinel','first_blocked_write':attempt[0],'actual_helper_main_application_executed':False,'producer_or_archive_writes':0,'temporary_isolated_parser_outputs_only':True,'protected_proof_sources':1167,'protected_site_assets':31,'protected_owner_ledgers':5,'protected_current_inventory_and_corrections_exact_before_after':True},
 'exact_two_step_parser_contract':ref(m.CONTRACT),'parser_results':[{'correction_id':s['correction_id'],'counts':d['counts'],'exact_changed_text_keys':s['exact_changed_text_keys'],'parsed_inventory_content_sha256':hashlib.sha256(raw).hexdigest()} for s,(raw,d,_) in zip(contract['steps'],parsed)],
 'focused_isolated_fixtures':fixtures,'fixture_count':len(fixtures),'exact_external_source_aliases':validated['exact_external_aliases'],'preserved_planning_history':{'original_parser_contract_helpers':[ref(Path('/tmp/root_prepare_source54_55_parser_contract27_v1.py')),ref(Path('/tmp/root_prepare_source54_55_parser_contract27_v2.py'))],'v1_real_failure_reason_reported_by_parent':'first planning reader incorrectly required a changed exercise at source54; final native parser has no changed source54 exercise','scope':'Original helper bytes preserved. No invented measured execution of that earlier planning failure.'},
 'preserved_actual_writer2_prewrite_guard_failure':{'entire_original_record_and_time':read(historyfiles[2]),'checker':ref(historyfiles[0]),'actual_runner':ref(historyfiles[1]),'raw_log':ref(historyfiles[3]),'scope':'Real reader1 reached both isolated full29 parser steps and failed before any producer write on sole external-resolved Normed.lean. Writer2 unchanged; writer3 only exact alias repair.'},'preserved_native_planning_reader1_failure_observation':{'reference':ref(historyfiles[4]),'entire_original_body_and_preservation_time':read(historyfiles[4])}, 'closed_evidence_sha256':closed,'scope':'Independent full writer/code and current native prewrite review only. No source correction, inventory update, owner rebase, whole exercise promotion or mathematical proof compilation executed. Real application belongs to Root after this concrete review.'}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','peer':str(OUT),'peer_sha256':sha(OUT),'fixtures':len(fixtures),'native_parser_steps':2,'first_write_blocked':True}))
