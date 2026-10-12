"""Record one genuine guarded TMP author preparation; no Lean/compiler/parser."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time

ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER=Path('/tmp/prepare-modules-owner31-current81-integral39-ast19-v2.py')
CONTEXT=Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
CONTEXT_SHA='f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
OUT=Path('/tmp/modules-owner31-current81-integral39-ast19-provisional-v1')
RECORD=Path('/tmp/modules-owner31-current81-Integral39-AST19-preparation-actual-v2.json')
LOG=RECORD.with_suffix('.log')

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert not RECORD.exists() and not LOG.exists() and not OUT.exists()
assert sha(CONTEXT)==CONTEXT_SHA
context=json.loads(CONTEXT.read_bytes())
pins={**context['pins_sha256'],**context['held_current_source_sha256'],**context['owners_sha256']}
helper_sha=sha(HELPER);wrapper_sha=sha(Path(__file__))
errors=[]
def guard():
    assert sha(CONTEXT)==CONTEXT_SHA and sha(HELPER)==helper_sha and sha(Path(__file__))==wrapper_sha
    for f,h in pins.items():
        p=ROOT/f
        assert not Path(f).is_absolute() and '..' not in Path(f).parts
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink() and sha(p)==h,f
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic();code=None
try:
    guard()
    with LOG.open('xb') as f:
        r=subprocess.run(['python3',str(HELPER)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
    code=r.returncode
except Exception as e:
    errors.append(repr(e))
    if not LOG.exists(): LOG.write_text(repr(e)+'\n')
try: guard()
except Exception as e: errors.append(repr(e))
finished=datetime.now(timezone.utc).isoformat();passed=code==0 and not errors
native={'status':'passed_actual_guarded_isolated_author_preparation' if passed else 'failed_actual_author_preparation_or_protection','actual_exit_code':code,'actual_wrapper_exit_code':0 if passed else 1,'actual_command':['python3',str(HELPER)],'actual_workdir':str(ROOT),'started_at_utc':started,'finished_at_utc':finished,'elapsed_seconds':time.monotonic()-tick,'helper':ref(HELPER),'original_actual_wrapper':ref(Path(__file__)),'raw_log':str(LOG),'raw_log_sha256':sha(LOG),'actual_source81_historical_source79_owner30_context':ref(CONTEXT),'protected_selected30_proof_sources':context['protected_selected30_proof_sources'],'unchanged_current81_final_css_book_assets':context['held_current81_final_css_book_assets'],'unchanged_historical_source79_raw_owner30_files':context['held_historical_source79_raw_owner30_files'],'guarded_unique_pins':len(pins),'protection_errors':errors,'Lean_or_HTML_parser_or_named_build_invoked':False,'canonical_owner_selection_or_publication_mutation':False,'coverage_complete':False}
with RECORD.open('x') as f:json.dump(native,f,indent=2);f.write('\n')
if passed:
    attached={'native':ref(RECORD),'raw_log':ref(LOG),'helper':ref(HELPER),'wrapper':ref(Path(__file__))}
    for stem in ['modules31-current81-provisional-independent-mapping-review-request','modules31-current81-provisional-root-offer']:
        original=OUT/(stem+'-v1.json');result=json.loads(original.read_bytes())
        result['status']='passed_actual_guarded_author_preparation_provisional_owner31_pending_actual39_canonical_pair_and_final_independent_mapping'
        result['original_pre_native_request_or_offer']=ref(original)
        result['actual_author_preparation']=attached
        if stem.endswith('root-offer'):
            result['request']=ref(OUT/'modules31-current81-provisional-independent-mapping-review-request-v2.json')
        new=OUT/(stem+'-v2.json')
        with new.open('x') as f:json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps({'native':ref(RECORD),'request':ref(OUT/'modules31-current81-provisional-independent-mapping-review-request-v2.json'),'offer':ref(OUT/'modules31-current81-provisional-root-offer-v2.json'),'actual_exit_code':code,'protection_errors':errors}))
else:
    print(json.dumps({'native':ref(RECORD),'actual_exit_code':code,'protection_errors':errors,'failed_outputs_preserved':True}))
raise SystemExit(0 if passed else 1)
