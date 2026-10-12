"""Independent full code/delta and actual native schema fixtures; no producer."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,tempfile,textwrap
R=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_bytes())
ref=lambda p:{'file':Path(p).relative_to(R).as_posix()if Path(p).is_relative_to(R)else str(p),'sha256':H(p)}
P=R/'book/coverage/checks/root_integrate_owner28_candidates_v6.py'
V3=R/'book/coverage/checks/root_integrate_owner28_candidates_v3.py'
OLDPEER=R/'book/coverage/checks/future28-core/owner28-installer-independent-applied-code-review-v3.json'
assert H(P)=='aa4340b7c42baeb3b5dc164d85fbfee936073d448e555f54e42d6e1e856cb37f'
assert H(V3)=='15aa2418ef2f716c36fcf9bfa94f57a0b2750ac7978200573a574aec6d73560f'
assert H(OLDPEER)=='c35b6ce275f8558a275a2648cdd6abac85dd92fdaca355604567fded7f9686da'
start=datetime.now(timezone.utc).isoformat();code=P.read_text();oldcode=V3.read_text();ast.parse(code)
oldtree=ast.parse(oldcode);newtree=ast.parse(code)
of={n.name:n for n in oldtree.body if isinstance(n,ast.FunctionDef)}
nf={n.name:n for n in newtree.body if isinstance(n,ast.FunctionDef)}
assert set(nf)-set(of)=={'native_record','proof_evidence'}
for name in set(of)-{'main','native_actual'}:assert ast.dump(of[name])==ast.dump(nf[name]),name
# Exact main delta preserves every prewrite invariant and the entire mutation block.
newmain=ast.get_source_segment(code,nf['main']);oldmain=ast.get_source_segment(oldcode,of['main'])
newmain=newmain.replace("native_record(native,command,str(ROOT/'verification/lean'),'passed')","assert native['command']==command and native['actual_workdir']==str(ROOT/'verification/lean')")
newmain=newmain.replace(",row['expected_actual_finalizer_status'])", ")")
fresh="""   pair=[p for p in all_pairs if p['source']['file']==n]
   assert len(pair)==2 and {p['kind'] for p in pair}=={'standalone','named'} and proof['actual_pair']==pair
   evidence=proof_evidence(proof,pair,closure)
   for path,digest in evidence.items():
    assert path not in immutable or immutable[path]==digest
    immutable[path]=digest
   for p in pair:
    for key in ('actual_record','raw_log','source_snapshot'):assert evidence[p[key]['file']]==p[key]['sha256']"""
prior="""   exact(proof['evidence_sha256']);immutable.update(proof['evidence_sha256'])
   pair=[p for p in all_pairs if p['source']['file']==n]
   assert len(pair)==2 and {p['kind'] for p in pair}=={'standalone','named'} and proof['actual_pair']==pair
   for p in pair:
    for key in ('actual_record','raw_log','source_snapshot'):assert proof['evidence_sha256'][p[key]['file']]==p[key]['sha256']"""
assert newmain.count(fresh)==1
assert newmain.replace(fresh,prior)==oldmain
def load(p,name):
    s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
m=load(P,'independent_installer28_native6');v4=load(R/'book/coverage/checks/root_integrate_owner28_candidates_v4.py','historical_native4');v5=load(R/'book/coverage/checks/root_integrate_owner28_candidates_v5.py','historical_native5')
selection=J(R/m.SELECTION);assert len(selection['proof_files'])==1175
inv=J(R/'book/coverage/inventory.json');assert H(R/'book/coverage/inventory.json')==m.INVENTORY_SHA
assets=dict(J(R/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256']);assets.update(inv['source_sha256']);assert len(assets)==31
protected={R/n:r['sha256']for n,r in selection['proof_files'].items()};protected.update({R/n:h for n,h in assets.items()});protected.update({R/'book/coverage'/f'{n}.json':h for n,h in m.OLD.items()})
batchpaths=[R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json',R/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json']
allpairs=[];closed=[P,V3,OLDPEER,*batchpaths]
for b in map(J,batchpaths):
    assert b['errors']==[] and len(b['actual_paired_records'])==b['actual_compiler_command_count']==2*b['source_count']
    for r in b['sources']:protected[R/r['canonical_source']]=r['original_tmp_source']['sha256']
    allpairs.extend(b['actual_paired_records'])
assert len(allpairs)==22 and len(protected)==1186+31+5
for p in [R/'book/coverage/inventory.json',R/'book/coverage/material-corrections.json',R/m.SELECTION,*closed]:protected[p]=H(p)
def guard():
    for p,h in protected.items():assert H(p)==h,str(p)
guard();cases=[]
def yes(name,fn):fn();cases.append({'name':name,'result':'accepted'})
def no(name,fn):
    try:fn()
    except (AssertionError,KeyError,TypeError,ValueError):cases.append({'name':name,'result':'rejected'})
    else:raise AssertionError('Unexpected acceptance: '+name)
module=J(R/'book/coverage/checks/modules-future28/current60-pair-bound-v1/modules28-current60-five-source-pair-bound-offer-draft-v5.json')
foundation=J(R/'book/coverage/checks/future28-foundations/current60-owner28-v1/foundations28-current60-final-offer-v1.json')
for label,offer in [('Module string',module),('Foundation dict',foundation)]:
    for n,proof in offer['proof_files'].items():
        pp=[p for p in allpairs if p['source']['file']==n];assert proof['actual_pair']==pp
        yes('real '+label+' proof evidence '+Path(n).stem,lambda proof=proof,pp=pp,offer=offer:m.proof_evidence(proof,pp,offer['required_evidence_artifacts_sha256']))
proof=next(iter(module['proof_files'].values()));pair=proof['actual_pair'];closure=module['required_evidence_artifacts_sha256'];ev={r[k]['file']:r[k]['sha256']for r in pair for k in ('actual_record','raw_log','source_snapshot')}
yes('original complete dict is retained exactly',lambda: (_ for _ in ()).throw(AssertionError()) if m.proof_evidence({'evidence_sha256':ev},pair,closure)!=ev else None)
yes('string derives only exact six logical native paths',lambda: (_ for _ in ()).throw(AssertionError()) if m.proof_evidence(proof,pair,closure)!=ev else None)
for value in [None,False,0,[],{},'','0'*64,proof['evidence_sha256'].upper(),{next(iter(ev)):next(iter(ev.values()))}]:no('unsupported or incomplete native proof evidence '+repr(value)[:100],lambda value=value:m.proof_evidence({'evidence_sha256':value},pair,closure))
for label,pp in [('missing named',pair[:1]),('duplicate standalone',[pair[0],pair[0]]),('tuple pair',tuple(pair))]:no(label,lambda pp=pp:m.proof_evidence(proof,pp,closure))
no('closure must be dict',lambda:m.proof_evidence(proof,pair,[]))
for k in ('actual_record','raw_log','source_snapshot'):
    bad=copy.deepcopy(pair);bad[0][k]['extra']=True
    no('wrong typed '+k+' shape',lambda bad=bad:m.proof_evidence(proof,bad,closure))
    cc=dict(closure);cc.pop(pair[0][k]['file']);no('missing closure '+k,lambda cc=cc:m.proof_evidence(proof,pair,cc))
    cc=dict(closure);cc[pair[0][k]['file']]='0'*64;no('wrong closure '+k,lambda cc=cc:m.proof_evidence(proof,pair,cc))
conflict=copy.deepcopy(pair);conflict[1]['source_snapshot']['sha256']='0'*64
no('same snapshot path conflicting digest',lambda:m.proof_evidence(proof,conflict,closure))
assert v5.proof_evidence({'evidence_sha256':{}},pair,closure)==ev
observation={'scope':'Actual pure-function observation only; installer5 producer never executed.','helper':ref(R/'book/coverage/checks/root_integrate_owner28_candidates_v5.py'),'original_empty_dict_was_accepted':True,'new6_empty_dict_rejected':True}
cmd=['python3','/tmp/exact-helper.py'];cwd=str(R)
base={'status':'exact_preserved_native_success_status','actual_exit_code':0,'exit_code':0,'actual_command':cmd,'command':cmd,'actual_workdir':cwd,'working_directory':cwd,'workdir':cwd,'cwd':cwd}
yes('all native aliases exact custom status',lambda:m.native_record(base,cmd,cwd,base['status']))
for key in ['actual_exit_code','exit_code']:no('false native exit '+key,lambda key=key:m.native_record({**base,key:False},cmd,cwd,base['status']))
for key in ['actual_command','command']:no('conflicting command '+key,lambda key=key:m.native_record({**base,key:['different']},cmd,cwd,base['status']))
for key in ['actual_workdir','working_directory','workdir','cwd']:no('conflicting native cwd '+key,lambda key=key:m.native_record({**base,key:'/tmp/wrong'},cmd,cwd,base['status']))
for status in ['',None,False,'passed','pending']:no('wrong exact status '+repr(status),lambda status=status:m.native_record(base,cmd,cwd,status))
no('missing native status',lambda:m.native_record({k:v for k,v in base.items()if k!='status'},cmd,cwd,base['status']))
for r in allpairs:
    d=m.checked(r['actual_record']);n=r['source']['file'];stem=Path(n).stem
    command=['lake','env','lean','SafeLearning/'+stem+'.lean']if r['kind']=='standalone'else['lake','build','SafeLearning.'+stem]
    m.native_record(d,command,str(R/'verification/lean'),'passed');assert d['source']==n and d['source_sha256_before']==d['source_sha256_after']==r['source']['sha256']
    for k in ('actual_record','raw_log','source_snapshot'):p=R/r[k]['file'];assert H(p)==r[k]['sha256'];closed.append(p)
offers=[J(R/'book/coverage/checks/future28-core/current60-identity-v1/core28-current60-identity-offer-canonical-v1.json'),J(R/'book/coverage/checks/applied-future28/current60-identity-v1/applied28-current60-identity-offer-canonical-v2.json'),foundation,J(R/'book/coverage/checks/future28-core/modules28-current60-final-pair-bound-independent-applied-review-v1.json')]
for i,o in enumerate(offers):
    r=o['actual_finalizer'];a=m.checked(r);lf=o.get('actual_finalizer_log_fields',['log','log_sha256']);aa=o['actual_finalizer_original_byte_aliases']
    yes('real owner finalizer exact native status '+str(i),lambda r=r,a=a,lf=lf,aa=aa:m.native_actual(r,a['actual_command'],a['helper_sha256_before'],lf,aa,a['status']))
    if i in (0,1):no('historical v4 rejects this actual authored status '+str(i),lambda a=a:v4.native_record(a,a['actual_command'],str(R)))
    closed.append(R/r['file'])
for n in ('current60-canonical-pairs28-execution-v1','current60-commissioning17-canonical-pair28-execution-v1'):
    p=R/'reports/full-coverage'/f'{n}.json';a=J(p);yes('real Root batch native '+n,lambda p=p,a=a:m.native_actual(ref(p),a['actual_command'],a['helper_sha256_before'],['log','log_sha256']));closed+=[p,R/a['log']]
# Same exact routing and closed-map prewrite clauses as the previous full reader.
routing=textwrap.dedent("  assert peer['status']==row['expected_final_mapping_peer_status']"+code.split("  assert peer['status']==row['expected_final_mapping_peer_status']",1)[1].split("  closure=offer['required_evidence_artifacts_sha256']",1)[0])
cr=module['candidate'];rr={'expected_final_mapping_peer_status':'passed','peer_candidate_pointer':['candidate'],'candidate':cr,'offer_candidate_pointer':['candidate']};peer={'status':'passed','errors':[],'candidate':cr};of={'candidate':cr,'inventory_sha256':m.INVENTORY_SHA}
def route(p,o):exec(routing,{'pointer':m.pointer,'INVENTORY_SHA':m.INVENTORY_SHA,'peer':p,'row':rr,'offer':o})
yes('exact candidate routing unchanged',lambda:route(peer,of));no('stale candidate peer',lambda:route({**peer,'candidate':{}},of));no('unapproved peer errors',lambda:route({**peer,'errors':['gap']},of));no('stale inventory',lambda:route(peer,{**of,'inventory_sha256':'0'*64}))
assert code.index('report=module.validate()')<code.index('archive=ARCHIVE+')<code.index("with safe(r['destination']).open('wb')")
guard()
OUT=Path('/tmp/owner28-installer-independent-applied-reader-v3.json');assert not OUT.exists()
d={'status':'passed_independent_full_owner28_installer_code_review','errors':[],'helper':ref(P),'helper_sha256':H(P),'review_started_at_utc':start,'review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'full_code_and_exact_main_delta_to_reviewed3':True,'actual_function_fixtures':cases,'original_full3_peer_body_and_time_retained':ref(OLDPEER),'original45_fixture_results_retained_without_new_execution_claim':J(OLDPEER).get('actual_function_fixtures',[]),'new_native_dictionaries_preserved_exact_strings_derived_strictly':True,'actual_eleven_source_native_schema_rows_checked':11,'actual_native_standalone_named_pairs_checked':22,'actual_owner_native_finalizer_records_checked':4,'actual_two_canonical_batch_records_checked':2,'all1186_source_current60_assets31_fiveowners_held':True,'unexecuted5_empty_dict_pure_function_observation':observation,'closed_evidence_sha256':{ref(p)['file']:H(p)for p in set(closed)},'conditional_scope':'Full static code and actual existing native/pure-function fixtures only. No installer main() binding preflight/apply, owner mutation, new Lean command, audit28, selection or publication execution. Root must independently execute its actual comprehensive candidate preflight.','coverage_complete':False}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'reader':ref(OUT),'new_fixtures':len(cases),'native_pairs':22,'native_owners':4}))
