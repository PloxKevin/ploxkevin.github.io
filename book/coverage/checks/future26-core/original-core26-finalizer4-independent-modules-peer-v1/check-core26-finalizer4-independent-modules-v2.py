from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,sys
R=Path('/home/oxrexkevin/SafetyBased');HELPER='book/coverage/checks/finalize_root_core26_offer_v4.py';P=R/HELPER;H=lambda p:hashlib.sha256((Path(p)if Path(p).is_absolute()else R/p).read_bytes()).hexdigest();assert H(HELPER)=='6159de7bc295d7f6a8ed9528085263387512f509ec36e3e6e16e5dda4a74fafb'
peer='book/coverage/checks/future26-core/composed-source53-v3/original-independent-candidate-peer/core26-composed-candidate-independent-foundations-confirmation-v1.json';t=ast.parse(P.read_text());stop=next(i for i,n in enumerate(t.body)if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and ast.unparse(n.value.func)=='archive.mkdir');prefix=t.body[:stop];assert not any(isinstance(n,ast.Call)and ast.unparse(n.func).endswith(('.mkdir','.open','.write_text'))for n in ast.walk(ast.Module(body=prefix,type_ignores=[])))
original=ast.parse((R/'book/coverage/checks/finalize_root_core26_offer_v3.py').read_text());normalized=copy.deepcopy(t)
assignment=next(n for n in normalized.body if isinstance(n,ast.Assign)and any(isinstance(k,ast.Name)and k.id=='HISTORICAL_REF_ALIASES' for k in n.targets))
assert isinstance(assignment.value,ast.Dict)
keep=[i for i,k in enumerate(assignment.value.keys)if not ast.literal_eval(k)[0].startswith('verification/lean/.lake/packages/mathlib/')]
assert len(keep)==4
assignment.value.keys=[assignment.value.keys[i]for i in keep];assignment.value.values=[assignment.value.values[i]for i in keep]
assert ast.dump(normalized,include_attributes=False)==ast.dump(original,include_attributes=False)
archive_actual='reports/full-coverage/archive-root-core26-mathlib-context-execution-v1.json';ad=json.loads((R/archive_actual).read_text())
assert type(ad['actual_exit_code'])is int and ad['actual_exit_code']==0
assert ad['helper_sha256_before']==ad['helper_sha256_after']
for n,h in ad['helper_sha256_after'].items():assert H(n)==h
assert H(ad['log'])==ad['log_sha256']
for n,h in [('verification/lean/.lake/packages/mathlib/Mathlib/Probability/CDF.lean','78586bddc289a171cbcb7fa155892333c4702c4f7f1185f9d6602ffac8b914e9'),('verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean','e2da9c2a5d8874cf2397cc98c114d678fc648e74d62d96c58ed546bcacdaa6be')]:
 assert H(n)==h
 assert (R/n).read_bytes()==(R/'book/coverage/checks/future26-core/composed-source53-v3/original-primary-mathlib-context'/Path(n).name).read_bytes()
oldargv=sys.argv;sys.argv=[HELPER,'--peer',peer,'--peer-sha256',H(peer)];ns={'__file__':str(P)}
try:exec(compile(ast.Module(body=prefix,type_ignores=[]),HELPER,'exec'),ns)
finally:sys.argv=oldargv
aliases=ns['HISTORICAL_REF_ALIASES'];assert len(aliases)==6;assert set(n for n,h in aliases)=={'book/coverage/core.json','book/coverage/inventory.json','SafeLearning/lyapunov-mpc.html','verification/lean/.lake/packages/mathlib/Mathlib/Probability/CDF.lean','verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean'}
for(n,h),target in aliases.items():assert H(target)==h
assert len(ns['proofs'])==4 and sum(r['public_export_count']for r in ns['proofs'].values())==48
for source,row in ns['proofs'].items():
 assert H(source)==row['sha256']
 for n,h in row['evidence_sha256'].items():assert H(n)==h
results=[]
def fixture(n,f,accept):
 try:f();a=True
 except(AssertionError,ValueError,TypeError,KeyError):a=False
 assert a==accept,(n,a);results.append({'name':n,'expected_accept':accept,'actual_accept':a,'scope':'Isolated read-only collection/guard; no finalizer execution.'})
for(original,h),target in aliases.items():
 fixture('exact authorized historical alias '+original+'@'+h[:8],lambda o=original,h=h:ns['collect']({'file':o,'sha256':h},{}),True)
 fixture('arbitrary hash rejected '+original,lambda o=original:ns['collect']({'file':o,'sha256':'0'*64},{}),False)
fixture('unapproved old inventory47 hash rejected',lambda:ns['collect']({'file':'book/coverage/inventory.json','sha256':'ab2b27355004f545180b00ca1c1d5243aeb88683100d6ca747e3054987bbf0c2'},{}),False)
fixture('unapproved mutable modules old hash rejected',lambda:ns['collect']({'file':'book/coverage/modules.json','sha256':'0'*64},{}),False)
fixture('actual bool false rejected',lambda:ns['zero']({'actual_exit_code':False}),False)
fixture('conflicting exits rejected',lambda:ns['zero']({'actual_exit_code':0,'exit_code':1}),False)
for p in ['/tmp/a','../outside','./book/coverage/core.json','book//coverage/core.json']:fixture('noncanonical path rejected '+p,lambda p=p:ns['safe'](p),False)
fixture('current legitimate inventory identity accepted',lambda:ns['collect']({'file':'book/coverage/inventory-after-correction53.json','sha256':'4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'},{}),True)
assert not ns['archive'].exists()and not(R/ns['OUT']).exists()
out={'status':'passed_independent_core26_finalizer4_full_delta_and_native_preflight_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':HELPER,'sha256':H(HELPER)},'helper_sha256':H(HELPER),'unexecuted_original_helpers_sha256':{p:H(p)for p in ['book/coverage/checks/finalize_root_core26_offer_v1.py','book/coverage/checks/finalize_root_core26_offer_v2.py','book/coverage/checks/finalize_root_core26_offer_v3.py']},'exact_authorized_six_historical_aliases':[{'original':{'file':n,'sha256':h},'immutable_original_byte_copy':{'file':target,'sha256':h}}for(n,h),target in aliases.items()],'native_candidate_peer':{'file':peer,'sha256':H(peer)},'native_proof_sources':4,'native_public_exports':48,'native_original_canonical_records':8,'complete_native_read_only_prewrite_prefix_passed':True,'all_original_body_time_refs_unchanged':True,'exact_v4_to_v3_only_two_primary_context_alias_delta':True,'actual_primary_context_archive':{'file':archive_actual,'sha256':H(archive_actual)},'retained_genuine_original_preflight_failure':{'actual_record':{'file':'/tmp/core26-finalizer3-independent-modules-actual-v1.json','sha256':H('/tmp/core26-finalizer3-independent-modules-actual-v1.json')},'scope':'Original real prewrite rejection of outside-root primary-library symlinks; no producer mutation.'},'fixture_count':len(results),'fixtures':results,'scope':'Independent complete code/delta read, genuine native prewrite guard-prefix execution and isolated accept/reject fixtures. No archive/output write, packaging/installation/compiler/global/aggregate execution inferred.'}
p=Path('/tmp/core26-finalizer4-independent-modules-review-v1.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':str(p),'sha256':H(p),'fixtures':len(results)}))
