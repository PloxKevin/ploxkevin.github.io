from pathlib import Path
import hashlib,json,re,datetime
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/modules-conformal45-source55-full-whole-review-request27-v1.json')
assert not OUT.exists()
def p(n):return Path(n) if n.startswith('/') else R/n
def sha(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def ref(n):return {'file':str(n),'sha256':sha(str(n))}
def rd(n):return json.loads(p(n).read_text())
P='/tmp/modules-conformal-source55-precision-proposal-v1.json';S='/tmp/modules-conformal-source55-independent-foundations-semantic-and-full29-parser-review-v1.json'
O='/tmp/modules-conformal8-three-answer-independent-foundations-full-source-review27-v1.json';Q='/tmp/modules-conformal8-three-answer-full-source-review-request27-v1.json'
proposal=rd(P);oldrequest=rd(Q);oldreview=rd(O);inv=rd('book/coverage/inventory.json')
assert sha('book/coverage/inventory.json')=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
trials=['/tmp/modules-conformal-continuous27-trial5.json','/tmp/modules-conformal-lexicographic-seeds-coverage27-trial3.json','/tmp/modules-conformal-common-uniform27-trial1.json']
expected=[8,28,9];sources=[];records=[];history=dict(oldrequest['evidence_sha256'])
for n,count in zip(trials,expected):
 t=rd(n);assert type(t['actual_exit_code']) is int and t['actual_exit_code']==0 and t['protection_errors']==[]
 source=t['source'];body=p(source).read_text();namespace=re.search(r'^namespace ([A-Za-z0-9_.]+)',body,re.M).group(1)
 names=re.findall(r'^theorem ([A-Za-z0-9_]+)',body,re.M);assert len(names)==count
 assert sha(source)==t['source_sha256_before']==t['source_sha256_after']==sha(t['source_snapshot'])==t['source_snapshot_sha256']
 assert sha(t['raw_log'])==t['raw_log_sha256'] and t['actual_command']==['lake','env','lean',source]
 assert 'sorry' not in body and 'axiom ' not in body
 sources.append({'source':ref(source),'entire_source':body,'public_theorem_count':count,'all_public_declarations':[namespace+'.'+name for name in names],'definition_count':len(re.findall(r'^def ',body,re.M)),'instance_count':len(re.findall(r'^instance ',body,re.M))})
 records.append({'record':ref(n),'entire_original_body_and_time':t,'raw_log':ref(t['raw_log']),'source_snapshot':ref(t['source_snapshot'])})
 for x in [n,source,t['raw_log'],t['source_snapshot'],t['original_actual_runner']['file']]:history[x]=sha(x)
for pattern in ['modules-conformal-lexicographic27-draft*.lean','modules-conformal-lexicographic-seeds27-draft*.lean','modules-conformal-lexicographic-seeds27-trial*.*','modules-conformal-lexicographic-seeds-coverage27-draft*.lean','modules-conformal-lexicographic-seeds-coverage27-trial*.*','modules-conformal-common-uniform27-draft*.lean','modules-conformal-common-uniform27-trial*.*']:
 for x in sorted(Path('/tmp').glob(pattern)):
  assert x.is_file() and not x.is_symlink();history[str(x)]=sha(str(x))
  if x.suffix=='.json':
   t=rd(str(x));assert type(t['actual_exit_code']) is int and t['actual_exit_code'] in (0,1) and t['protection_errors']==[]
   assert sha(t['source'])==sha(t['source_snapshot'])==t['source_sha256_before']==t['source_sha256_after']==t['source_snapshot_sha256']
   assert sha(t['raw_log'])==t['raw_log_sha256']
for n in [P,S,O,Q,'book/coverage/inventory.json','book/coverage/modules.json','reports/full-coverage/checkpoint-26-selection.json',__file__]:history[n]=sha(n)
for n,b in oldrequest['selected_actual_source_bodies'].items():assert sha(n)==b['sha256'] and p(n).read_text()==b['entire_source']
sel=rd('reports/full-coverage/checkpoint-26-selection.json');guard={**{n:v['sha256'] for n,v in sel['proof_files'].items()},**inv['source_sha256'],**records[-1]['entire_original_body_and_time']['installed26_owner_sha256']}
for n,s in guard.items():assert sha(n)==s
keys=['verification.html::node-'+str(i) for i in [1176,1180,1182,1183,1184]]
oldunits=[next(u for u in inv['material_source_units'] if u['key']==key) for key in keys]
virtual=[]
for u in oldunits:
 if u['key']=='verification.html::node-1184':virtual.append(proposal['proposed_entire_material_record'])
 else:virtual.append({**u,'source_sha256':proposal['candidate_only']['sha256']})
ex=next(e for e in inv['exercises'] if e['key']=='verification.html::exercise-17')
vex={**ex,'source_sha256':proposal['candidate_only']['sha256'],'source_text':proposal['proposed_exercise_text'],'text_sha256':hashlib.sha256(proposal['proposed_exercise_text'].encode()).hexdigest()}
request={'status':'actual_tmp45_bodies_request_fresh_full_virtual_source55_conformal_exercise_and_five_literals_no_approval_inferred','prepared_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'three_entire_actual_sources':sources,'total_public_theorem_count':45,'genuine_successful_standalone_records':records,'original_current53_entire_exercise':ex,'proposed_source55_entire_exercise':vex,'original_current53_entire_units':oldunits,'proposed_source55_entire_units':virtual,'source55_proposal':{'record':ref(P),'entire_original_body_and_time':proposal},'source55_independent_semantic_and_full29_parser_peer':{'record':ref(S),'entire_original_body_and_time':rd(S)},'original_eight_body_three_answer_peer':{'record':ref(O),'entire_original_body_and_time':oldreview},'entire_original_eight_body_request':oldrequest,'selected_actual_source_bodies':oldrequest['selected_actual_source_bodies'],'original_current_material_rows_and_times':oldrequest['old_material_rows_preserved'],'proposed_new_precise_groups':[{'component_id':'actual_iid_uniform_seed_joint_law','reason':'Actual volume restricted to[0,1] is a probability law and atomless; its finite product is an iid law independent of the original score law. Coordinate permutation preserves that product. Measurable attachment constructs actual score-seed pair law, preserves genuine permutation exchangeability and proves a.s. injectivity.'},{'component_id':'actual_finite_lexicographic_uniform_ranks','reason':'Measurable lex comparisons, strict finite rank/bijection, exact-one rank occurrence and finite indicator integration derive uniform ranks from the actual exchangeable pair law, with no uniform-rank premise.'},{'component_id':'actual_calibration_membership_and_tied_lower_bound','reason':'Pair rank equals the count of only other calibration pairs preceding the test pair. Strict raw-score count is bounded by it. The original genuine calibrationThreshold membership characterization gives event inclusion. Forgetting seeds recovers the exact original law; monotone probability yields actual raw coverage≥k/(n+1), then≥1−alpha.'},{'component_id':'consistent_randomized_calibration_and_prediction_upper_bound','reason':'The actual calibration-only pair comparison rule has exact seeded CDF k/(n+1), and the actual ceiling rank yields both lower and strict upper bounds. No separate independent rank or no-ties conclusion is assumed.'},{'component_id':'actual_common_uniform_continuous_marginal_countermodel','reason':'The joint common-score law is induced by one actual Uniform[0,1] draw shared by every coordinate. It is exchangeable, each marginal is exactly uniform with explicit continuous CDF and zero singleton mass, yet every pair of coordinates ties a.s. Actual n9/k9 calibration coverage is1, contradicting the strict upper bound. This supplements the original constant-score counterexample.'}],'remaining_scope_prerequisites':['Reviewer must read every full source, entire current and proposed literal/parent/Section5, primaryD1/D2 and original selected rank/calibration proof sources.','Only the corrected virtual Source55 answer(d) can receive complete approval now; no actual current-source correction or current ledger promotion is inferred.','Independent uniforms are constructed by a genuine product measure independent of the arbitrary original exchangeable score law. No iid original-score assumption replaces exchangeability.','k=ceil((n+1)(1−alpha))≤n and alpha≤1 are explicit bounds; the literal probability level lies in[0,1]. Infinite-threshold k>n is outside this exercise target.','Original7bef body/time/a-b-c decisions and all genuine old failed/passed source snapshots/logs remain exact.'],'evidence_sha256':history,'protected_counts':{'selected_sources':1167,'current_assets':31,'installed26_owner_files':5},'scope':'TMP-only full source review request. No semantic approval, compiler rerun, canonical/named pair, owner integration, Source55 application, selection or aggregate claim.'}
for n,s in history.items():assert sha(n)==s
OUT.write_text(json.dumps(request,indent=2,ensure_ascii=False)+'\n')
for n,s in guard.items():assert sha(n)==s
print(json.dumps({'request':ref(str(OUT)),'actual_sources':3,'public_theorems':45,'whole_decision_requested_on_virtual_source55_only':True,'history_artifacts':len(history)}))
