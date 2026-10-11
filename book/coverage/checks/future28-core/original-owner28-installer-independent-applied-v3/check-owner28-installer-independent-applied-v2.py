"""Full-code/delta and actual native/isolated-function guard review, no producer."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,sys,tempfile,textwrap
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();J=lambda p:json.loads(p.read_bytes());ref=lambda p:{'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':H(p)}
P=R/'book/coverage/checks/root_integrate_owner28_candidates_v3.py';V2=R/'book/coverage/checks/root_integrate_owner28_candidates_v2.py';V1=R/'book/coverage/checks/root_integrate_owner28_candidates_v1.py'
assert H(P)=='15aa2418ef2f716c36fcf9bfa94f57a0b2750ac7978200573a574aec6d73560f';assert H(V2)=='0223b512f0afbc029df403eb1f65ab4f08819ebfd3649aafdb95ffc28df47864';assert H(V1)=='bfed31849a2bea7e148508babe97e06ec2aacf1c851769096146c686f5f93204'
start=datetime.now(timezone.utc).isoformat();code=P.read_text();prior=V2.read_text();needle=" assert d[log_fields[0]] not in helpers or helpers[d[log_fields[0]]]==d[log_fields[1]]\n"
assert code.count(needle)==1 and code.replace(needle,'',1)==prior
spec=importlib.util.spec_from_file_location('independent_installer28',P);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
sel=J(R/m.SELECTION);inv=J(R/'book/coverage/inventory.json');assert len(sel['proof_files'])==1175 and H(R/'book/coverage/inventory.json')==m.INVENTORY_SHA
assets=dict(J(R/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256']);assets.update(inv['source_sha256']);assert len(assets)==31
protected={n:r['sha256']for n,r in sel['proof_files'].items()};protected.update(assets);protected.update({'book/coverage/'+n+'.json':h for n,h in m.OLD.items()})
batchpaths=[R/'book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json',R/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1/actual-current60-commissioning17-canonical-paired-readiness28-v1.json']
batches=[J(p)for p in batchpaths];allpairs=[];closed=[P,V1,V2,Path('/tmp/owner28-installer2-native-path-collision-observation-v1.json'),*batchpaths]
for b in batches:
 assert b['errors']==[] and b['actual_compiler_command_count']==2*b['source_count']==len(b['actual_paired_records'])
 for row in b['sources']:protected[row['canonical_source']]=row['original_tmp_source']['sha256']
 allpairs+=b['actual_paired_records']
assert len(protected)==1186+31+5 and len(allpairs)==22 and sum(b['public_theorem_count']for b in batches)==252
for p in [R/'book/coverage/inventory.json',R/'book/coverage/material-corrections.json',R/m.SELECTION,*closed]:protected[str(p.relative_to(R))if p.is_relative_to(R)else str(p)]=H(p)
def guard():
 for n,h in protected.items():p=Path(n)if Path(n).is_absolute()else R/n;assert H(p)==h,n
guard();cases=[]
def accepted(name,fn):fn();cases.append({'name':name,'result':'accepted'})
def rejected(name,fn):
 try:fn()
 except (AssertionError,KeyError,TypeError,ValueError):cases.append({'name':name,'result':'rejected'})
 else:raise AssertionError('Unexpected acceptance: '+name)
accepted('strict all-present three integer exit aliases',lambda:m.zero({'actual_exit_code':0,'exit_code':0,'actual_runner_exit_code':0}))
for d in [{},{'actual_exit_code':False},{'exit_code':True},{'actual_exit_code':0,'exit_code':False},{'actual_exit_code':0,'actual_runner_exit_code':1},{'actual_exit_code':0.0}]:rejected('unsupported native exit aliases '+repr(d),lambda d=d:m.zero(d))
accepted('safe canonical Root helper path',lambda:m.safe(str(P.relative_to(R))))
for n in ['/tmp/unapproved.json','../outside','book//coverage/core.json','book/coverage/../../outside','']:
 rejected('unsafe Root path '+repr(n),lambda n=n:m.safe(n))
actuals=[R/'reports/full-coverage/current60-canonical-pairs28-execution-v1.json',R/'reports/full-coverage/current60-commissioning17-canonical-pair28-execution-v1.json']
for p in actuals:
 a=J(p);accepted('real Root canonical batch native '+p.name,lambda p=p,a=a:m.native_actual(ref(p),a['actual_command'],a['helper_sha256_before'],['log','log_sha256']));closed+=[p,R/a['log']]
applied=J(R/'book/coverage/checks/applied-future28/current60-identity-v1/applied28-current60-identity-offer-canonical-v1.json');aliases=applied['original_closed_byte_aliases'];ar=applied['actual_isolated_candidate_preparation'];a=m.checked(ar);native_names=set(a['helper_sha256_before'])|{a['log']};native_alias={n:aliases[n]for n in native_names}
accepted('real preserved Applied absolute-native helper/log with typed durable aliases',lambda:m.native_actual(ar,a['actual_command'],a['helper_sha256_before'],['log','log_sha256'],native_alias))
accepted('real complete Applied canonical reviewed evidence closure',lambda:m.exact(applied['required_evidence_artifacts_sha256']))
for row in allpairs:
 n=row['source']['file'];h=row['source']['sha256'];native=m.checked(row['actual_record']);m.zero(native);stem=Path(n).stem
 assert type(row['actual_exit_code'])is int and row['actual_exit_code']==0
 cmd=['lake','env','lean','SafeLearning/'+stem+'.lean']if row['kind']=='standalone'else['lake','build','SafeLearning.'+stem]
 assert native['command']==cmd and native['actual_workdir']==str(R/'verification/lean') and native['source']==n and native['source_sha256_before']==native['source_sha256_after']==h
 assert row['raw_log']=={'file':native['log'],'sha256':native['log_sha256']}and row['source_snapshot']['sha256']==h
 for key in ['actual_record','raw_log','source_snapshot']:r=row[key];assert m.sha(r['file'])==r['sha256'];closed.append(R/r['file'])
# Execute the exact routing and closure clauses from the real main function.
routing=textwrap.dedent("  assert peer['status']==row['expected_final_mapping_peer_status']"+code.split("  assert peer['status']==row['expected_final_mapping_peer_status']",1)[1].split("  closure=offer['required_evidence_artifacts_sha256']",1)[0])
def route(peer,row,offer):exec(routing,{'pointer':m.pointer,'INVENTORY_SHA':m.INVENTORY_SHA,'peer':peer,'row':row,'offer':offer})
cr=applied['candidate'];row={'expected_final_mapping_peer_status':'passed','peer_candidate_pointer':['candidate'],'candidate':cr,'offer_candidate_pointer':['candidate']};peer={'status':'passed','errors':[],'candidate':cr};offer={'candidate':cr,'inventory_sha256':m.INVENTORY_SHA}
accepted('exact typed independent candidate and owner offer routing',lambda:route(peer,row,offer))
for label,p,o in [('wrong status',{**peer,'status':'pending'},offer),('nonempty errors',{**peer,'errors':['gap']},offer),('wrong peer candidate',{**peer,'candidate':ar},offer),('wrong offer candidate',peer,{**offer,'candidate':ar}),('stale current60 inventory',peer,{**offer,'inventory_sha256':'0'*64})]:rejected(label,lambda p=p,o=o:route(p,row,o))
closureblock=textwrap.dedent("  closure=offer['required_evidence_artifacts_sha256']"+code.split("  closure=offer['required_evidence_artifacts_sha256']",1)[1].split("  assert pointer(peer,row['peer_actual_finalizer_pointer'])",1)[0])
def merge(closure,immutable):exec(closureblock,{'offer':{'required_evidence_artifacts_sha256':closure},'immutable':immutable,'exact':m.exact})
one={str(P.relative_to(R)):H(P)};accepted('exact nonempty evidence closure merged',lambda:merge(one,{}));rejected('missing evidence closure',lambda:merge({},{}));rejected('wrong evidence digest',lambda:merge({next(iter(one)):'0'*64},{}));rejected('conflicting prior evidence SHA',lambda:merge(one,{next(iter(one)):'0'*64}))
pairblock=textwrap.dedent(code.split('   pair=[p for p in all_pairs if p[\'source\'][\'file\']==n]',1)[1].split('  replacements.append(',1)[0]);pairblock="pair=[p for p in all_pairs if p['source']['file']==n]"+pairblock
n=allpairs[0]['source']['file'];pair=[p for p in allpairs if p['source']['file']==n];ev={r[k]['file']:r[k]['sha256']for r in pair for k in ['actual_record','raw_log','source_snapshot']}
def paired(rows,proof):exec(pairblock,{'n':n,'all_pairs':rows,'proof':proof})
proof={'actual_pair':pair,'evidence_sha256':ev};accepted('real source exact standalone and named pair evidence',lambda:paired(pair,proof));rejected('missing named pair',lambda:paired(pair[:1],proof));duplicate=[copy.deepcopy(pair[0]),copy.deepcopy(pair[0])];rejected('two standalone rows',lambda:paired(duplicate,{**proof,'actual_pair':duplicate}));rejected('peer metadata mismatched native pair',lambda:paired(pair,{**proof,'actual_pair':[]}));rejected('omitted exact pair raw evidence',lambda:paired(pair,{**proof,'evidence_sha256':{}}))
with tempfile.TemporaryDirectory(prefix='owner28-isolated-native-alias-')as td:
 T=Path(td);m.ROOT=T;(T/'helper').write_bytes(b'exact helper');(T/'log').write_bytes(b'exact log');hh=H(T/'helper');lh=H(T/'log');names={'/tmp/owner28-fixture-helper.py':hh};cmd=['python3',next(iter(names))];base={'actual_exit_code':0,'actual_command':cmd,'actual_workdir':str(T),'helper_sha256_before':names,'helper_sha256_after':names,'log':'/tmp/owner28-fixture.log','log_sha256':lh};aa={next(iter(names)):{'file':'helper','sha256':hh},base['log']:{'file':'log','sha256':lh}}
 def native(data,aliases):
  (T/'native.json').write_text(json.dumps(data));return m.native_actual({'file':'native.json','sha256':H(T/'native.json')},cmd,names,['log','log_sha256'],aliases)
 accepted('synthetic exact /tmp helper/log aliases',lambda:native(base,aa))
 rejected('missing absolute log alias',lambda:native(base,{next(iter(names)):aa[next(iter(names))]}))
 rejected('extra alias authorization',lambda:native(base,{**aa,'/tmp/extra':aa[base['log']]}))
 rejected('wrong copied helper digest',lambda:native(base,{**aa,next(iter(names)):{'file':'log','sha256':lh}}))
 bad=copy.deepcopy(base);bad['actual_exit_code']=False;rejected('native false integer alias',lambda:native(bad,aa))
 bad=copy.deepcopy(base);bad['actual_command']=['python3','/tmp/different'];rejected('wrong native actual command',lambda:native(bad,aa))
 bad=copy.deepcopy(base);bad['actual_workdir']='/tmp/different';rejected('wrong actual workdir',lambda:native(bad,aa))
 bad=copy.deepcopy(base);bad['helper_sha256_after']={next(iter(names)):'0'*64};rejected('changed helper after execution',lambda:native(bad,aa))
 collision=copy.deepcopy(base);collision['log']=next(iter(names));collision['log_sha256']=lh;rejected('different helper/log original same-path digests',lambda:native(collision,{next(iter(names)):{'file':'log','sha256':lh}}))
 equal=copy.deepcopy(base);equal['log']=next(iter(names));equal['log_sha256']=hh;accepted('same original path allowed only identical helper/log digest',lambda:native(equal,{next(iter(names)):{'file':'helper','sha256':hh}}))
 bad=copy.deepcopy(base);bad['log']='/etc/unsupported';rejected('absolute original outside TMP',lambda:native(bad,{next(iter(names)):aa[next(iter(names))],bad['log']:aa[base['log']]}))
 (T/'linked').symlink_to(T/'helper');rejected('symlink canonical helper byte alias',lambda:native(base,{**aa,next(iter(names)):{'file':'linked','sha256':hh}}))
 (T/'helper').write_bytes(b'stale');rejected('changed canonical alias bytes',lambda:native(base,aa));m.ROOT=R
guard()
# Archive-before-install and complete validator preflight precede any production write.
assert code.index('report=module.validate()')<code.index('archive=ARCHIVE+')<code.index("with safe(r['destination']).open('wb')")
assert code.index('assert not set(immutable).intersection')<code.index('report=module.validate()')
closed.extend([Path('/tmp/check-owner28-installer-independent-applied-v1.py'),Path('/tmp/run-owner28-installer-independent-applied-v1.py'),Path('/tmp/owner28-installer-independent-applied-actual-v1.json'),Path('/tmp/owner28-installer-independent-applied-actual-v1.log')]);unique={str(p):p for p in closed};OUT=Path('/tmp/owner28-installer-independent-applied-reader-v2.json');assert not OUT.exists()
d={'status':'passed_independent_full_owner28_installer_code_review','errors':[],'helper':ref(P),'helper_sha256':H(P),'review_started_at_utc':start,'review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'full_code_read_and_exact_v3_delta':True,'all_fixed_v1_v2_native_closure_findings_resolved':True,'actual_function_fixtures':cases,'actual_two_canonical_batch_records_checked':2,'actual_native_standalone_named_pairs_checked':22,'actual_new_source_count':11,'actual_public_theorem_count':252,'native_existing_Applied_absolute_provenance_checked':True,'all1186_source_current60_assets31_fiveowners_before_after_held':True,'conditional_scope':'Full code and actual native/pure-function fixtures. No concrete four-owner binding exists yet, no producer main() preflight/apply, owner install, Lean or publication execution claimed. Root must separately check real binding and comprehensive candidate preflight.','original_v2_collision_finding':ref(Path('/tmp/owner28-installer2-native-path-collision-observation-v1.json')),'closed_evidence_sha256':{ref(p)['file']:H(p)for p in unique.values()},'preserved_own_reader1_failure':'Original checker1 failed only because the isolated extracted routing block lost one indentation space. No Root helper defect or producer execution; NEW checker2 dedents the complete original block. Original checker/runner/actual1/raw retained unchanged.','live_owner_written':False,'coverage_complete':False}
with OUT.open('x')as f:f.write(json.dumps(d,indent=2)+'\n')
print(json.dumps({'status':d['status'],'reader':ref(OUT),'fixtures':len(cases),'actualpairs':22}))
