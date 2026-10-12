"""Measure genuine TMP binding with Source81/raw30 and all new6 sources guarded."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess,time
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER=Path('/tmp/bind-modules-owner31-current81-actual-Integral39-pair-v1.py')
CONTEXT=Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
CONTEXT_SHA='f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
READY=ROOT/'book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json'
READY_SHA='c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520'
OUT=Path('/tmp/modules-owner31-current81-integral39-ast19-actual-pair-v1')
RECORD=Path('/tmp/modules-owner31-current81-Integral39-actual-pair-binding-actual-v1.json');LOG=RECORD.with_suffix('.log')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert not RECORD.exists() and not LOG.exists() and not OUT.exists()
assert sha(CONTEXT)==CONTEXT_SHA and sha(READY)==READY_SHA
context=json.loads(CONTEXT.read_bytes());ready=json.loads(READY.read_bytes())
pins={**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256'],**ready['protected_inputs_sha256']}
new_sources={r['canonical_source']:r['original_tmp_source']['sha256'] for r in ready['sources']};assert len(new_sources)==6;pins.update(new_sources)
helper_sha=sha(HELPER);wrapper_sha=sha(Path(__file__));errors=[]
def guard():
    assert sha(CONTEXT)==CONTEXT_SHA and sha(READY)==READY_SHA and sha(HELPER)==helper_sha and sha(Path(__file__))==wrapper_sha
    for f,h in pins.items():
        p=ROOT/f;assert p.resolve().is_relative_to(ROOT) and not p.is_symlink() and sha(p)==h,f
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();code=None
try:
    guard()
    with LOG.open('xb') as f:r=subprocess.run(['python3',str(HELPER)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
    code=r.returncode
except Exception as e:
    errors.append(repr(e))
    if not LOG.exists():LOG.write_text(repr(e)+'\n')
try:guard()
except Exception as e:errors.append(repr(e))
finished=datetime.now(timezone.utc).isoformat();passed=code==0 and not errors
native={'status':'passed_actual_guarded_isolated_pair_binding' if passed else 'failed_actual_pair_binding_or_protection','actual_exit_code':code,'actual_wrapper_exit_code':0 if passed else 1,'actual_command':['python3',str(HELPER)],'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'helper':ref(HELPER),'original_actual_wrapper':ref(Path(__file__)),'raw_log':str(LOG),'raw_log_sha256':sha(LOG),'actual_source81_historical_source79_owner30_context':ref(CONTEXT),'actual_Root_complete12_readiness':ref(READY),'protected_selected30_proof_sources':1242,'new6_canonical_sources_guarded':new_sources,'unchanged_current81_final_css_book_assets':31,'unchanged_historical_source79_raw_owner30_files':5,'guarded_unique_pins':len(pins),'protection_errors':errors,'Lean_HTML_parser_or_named_build_invoked':False,'canonical_owner_selection_or_publication_mutation':False,'coverage_complete':False}
with RECORD.open('x') as f:json.dump(native,f,indent=2);f.write('\n')
if passed:
    attached={'native':ref(RECORD),'raw_log':ref(LOG),'helper':ref(HELPER),'wrapper':ref(Path(__file__))}
    for stem in ['modules31-current81-actual-pair-independent-final-mapping-review-request','modules31-current81-actual-pair-root-offer']:
        original=OUT/(stem+'-v1.json');result=json.loads(original.read_bytes());result['status']='passed_actual_guarded_author_pair_binding_final_owner31_mapping_request_pending_independent_review_and_Root_installation'
        result['original_pre_native_request_or_offer']=ref(original);result['actual_author_pair_binding']=attached
        if stem.endswith('root-offer'):result['request']=ref(OUT/'modules31-current81-actual-pair-independent-final-mapping-review-request-v2.json')
        new=OUT/(stem+'-v2.json')
        with new.open('x') as f:json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps({'native':ref(RECORD),'request':ref(OUT/'modules31-current81-actual-pair-independent-final-mapping-review-request-v2.json'),'offer':ref(OUT/'modules31-current81-actual-pair-root-offer-v2.json'),'actual_exit_code':code,'protection_errors':errors}))
else:print(json.dumps({'native':ref(RECORD),'actual_exit_code':code,'protection_errors':errors,'failed_outputs_preserved':True}))
raise SystemExit(0 if passed else 1)
