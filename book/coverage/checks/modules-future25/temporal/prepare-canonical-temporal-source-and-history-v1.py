from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/modules-future25/temporal'
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ref=lambda p:{'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':H(p)}
def newwrite(p,data):
 assert not p.exists(),str(p)
 p.write_bytes(data)
def readj(p):return json.loads(p.read_text())
selection=readj(ROOT/'reports/full-coverage/checkpoint-24-selection.json')
assert len(selection['proof_files'])==1144
before={f:H(ROOT/f) for f in selection['proof_files']}
assert all(before[f]==row['sha256'] for f,row in selection['proof_files'].items())
ownerpaths=['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json','book/coverage/inventory.json']
owners={p:H(ROOT/p) for p in ownerpaths}
assert owners['book/coverage/modules.json']=='1d4395c5b7cb9dc18217b0c4236a04868f67a2445d0ffed18f3a77215d3b2c90'
assert owners['book/coverage/inventory.json']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
request=Path('/tmp/modules-temporal25-source-component-review-request-v1.json');r=readj(request)
first=Path('/tmp/modules-doubly-hyperdominant24-trial6.lean');second=Path('/tmp/modules-temporal-diagonal24-trial2.lean')
assert H(first)=='fbfd13157c32a410f65c03d4b4aba9795fabb4ec0a2a0f293c2dc10992f13682'
a=first.read_text();b=second.read_text();assert b.startswith(a)
old1='SafeLearning.CompleteModulesNNDoublyHyperdominant24';new1='SafeLearning.CompleteModulesNNDoublyHyperdominant25'
old2='SafeLearning.CompleteModulesNNTemporalDiagonal24';new2='SafeLearning.CompleteModulesNNTemporalDiagonal25'
source1=a.replace(old1,new1)
source2=('import SafeLearning.CompleteModulesNNDoublyHyperdominant25\n\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\nset_option maxHeartbeats 1200000\nnoncomputable section\nopen Matrix Set\nopen scoped BigOperators\n'+b[len(a):].lstrip()).replace(old1,new1).replace(old2,new2)
assert source1.replace(new1,old1)==a
assert source2.split('namespace '+new2,1)[1].replace(new1,old1).replace(new2,old2)==b[len(a):].split('namespace '+old2,1)[1]
files=[]
for name,text,oldbody in [('CompleteModulesNNDoublyHyperdominant25',source1,a),('CompleteModulesNNTemporalDiagonal25',source2,b[len(a):])]:
 p=ROOT/'verification/lean/SafeLearning'/f'{name}.lean';newwrite(p,text.encode());snap=BASE/'sources'/f'{name}-source-v1.lean';newwrite(snap,p.read_bytes())
 ds=declarations(text);exports=[d['name'] for d in ds if d['kind'] in ('theorem','lemma')]
 files.append({'source':ref(p),'source_snapshot':ref(snap),'public_theorems':exports,'all_public_and_definition_names':ds,'original_source_body':oldbody,'transformation':'Exact proof/statement bodies retained; first namespace uniquely renamed25, second extracts only the original temporal namespace and imports the new first module.'})
assert [len(f['public_theorems']) for f in files]==[6,3]
explicit=[request,Path('/tmp/modules-temporal25-independent-foundations-full-component-review-v1.json'),Path('/tmp/check-modules-temporal25-independent-foundations-full-component-review-v1.py'),Path('/tmp/run-modules-temporal25-independent-foundations-full-component-review-v1.py'),Path('/tmp/modules-temporal25-independent-foundations-full-component-review-actual-v1.json'),Path('/tmp/modules-temporal25-independent-foundations-full-component-review-actual-v1.log'),Path('/tmp/modules-nn-corrected52-answer-b-full-source-review-request25-v1.json'),Path('/tmp/modules-nn-corrected52-answer-b-independent-foundations-full-source-review25-v1.json'),Path('/tmp/check-modules-corrected52-answer-b-independent-foundations-full-review25-v1.py'),Path('/tmp/run-modules-corrected52-answer-b-independent-foundations-full-review25-v1.py'),Path('/tmp/modules-corrected52-answer-b-independent-foundations-full-review25-actual-v1.json'),Path('/tmp/modules-corrected52-answer-b-independent-foundations-full-review25-actual-v1.log'),Path('/tmp/modules-nn-answer-b-selected-universal-monotonicity-evidence-supplement25-v1.json'),Path('/tmp/check-modules-answer-b-selected-monotonicity-supplement25-v1.py'),Path('/tmp/run-modules-answer-b-selected-monotonicity-supplement25-v1.py'),Path('/tmp/modules-answer-b-selected-monotonicity-supplement25-actual-v1.json'),Path('/tmp/modules-answer-b-selected-monotonicity-supplement25-actual-v1.log')]
for history in r['all_actual_failed_and_passed_trial_history']:
 body=history['entire_original_actual_record_body_and_time']
 for k in ['actual_record','source_snapshot','raw_log','runner']:
  q=history[k];p=Path(q['file']);assert H(p)==q['sha256'];explicit.append(p)
 source=Path(body['source']);assert H(source)==body['source_sha256_after']==body['source_sha256_before'];explicit.append(source)
for src in r['actual_sources']:explicit.append(Path(src['source']['file']))
aliases={}
for p in sorted(set(explicit)):
 assert p.is_file(),str(p)
 dest=BASE/'original-tmp-v1'/p.name
 newwrite(dest,p.read_bytes());assert H(dest)==H(p)
 aliases[str(p)]={'canonical_exact_byte_copy':ref(dest),'size_bytes':p.stat().st_size,'purpose':'Original closed source, trial, independent full/component review, checker, runner, actual record or raw log; original body/command/time unchanged.'}
assert [h['entire_original_actual_record_body_and_time']['actual_exit_code'] for h in r['all_actual_failed_and_passed_trial_history']]==[1,1,1,1,1,0,1,0]
assert owners=={p:H(ROOT/p) for p in ownerpaths};assert before=={f:H(ROOT/f) for f in before}
result={'status':'exact_reviewed_TMP_bodies_transferred_to_two_distinct_future25_canonical_sources_and_history_bytes_preserved','created_at_utc':datetime.now(timezone.utc).isoformat(),'source_files':files,'original_path_exact_byte_aliases':aliases,'original_component_peer':aliases['/tmp/modules-temporal25-independent-foundations-full-component-review-v1.json']['canonical_exact_byte_copy'],'original_whole_answer_b_peer':aliases['/tmp/modules-nn-corrected52-answer-b-independent-foundations-full-source-review25-v1.json']['canonical_exact_byte_copy'],'original_selected_universal_monotonicity_supplement':aliases['/tmp/modules-nn-answer-b-selected-universal-monotonicity-evidence-supplement25-v1.json']['canonical_exact_byte_copy'],'all_eight_genuine_original_trial_records_and_times_preserved':True,'current24_owner_inventory_sha256_before_after_exact':owners,'all1144_selected24_proof_sources_before_after_exact':True,'no_new_compiler_execution_yet':True,'scope':'Canonical source/history preparation only. Original semantic decisions/time untouched; new actual standalone/named pairs required. Nine public temporal declarations are precise components, not whole answer(c) or Exercise20.'}
newwrite(BASE/'canonical-source-and-original-history-preparation-v1.json',(json.dumps(result,indent=2,ensure_ascii=False)+'\n').encode());print(json.dumps({'output':str(BASE/'canonical-source-and-original-history-preparation-v1.json'),'sha256':H(BASE/'canonical-source-and-original-history-preparation-v1.json'),'original_file_copies':len(aliases),'public_theorems':9,'sources':[f['source'] for f in files]}))
