from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
R=Path('/home/oxrexkevin/SafetyBased');Q=Path('/tmp/foundations-normcomparison8-full-literal-request29-v1.json');O=Path('/tmp/foundations-normcomparison8-independent-modules29-peer-original-v1.json');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not O.exists() and sha(Q)=='2131f4b0d9c3ec3359408ce4a9a5672d3d1602e8eb105548c230c6a38a477aa2'
start=datetime.now(timezone.utc).isoformat();q=json.loads(Q.read_bytes())
def read(v):
 p=Path(v['file']);assert sha(p)==v['sha256']and p.stat().st_size==v['bytes'];return p
p=read(q['proof_source']);s=p.read_text();assert s==q['entire_eight_source_bodies_and_definitions']
assert re.findall(r'^theorem (\w+)',s,re.M)==q['public_theorem_names']and q['public_theorem_count']==8
inv=json.loads((R/'book/coverage/inventory.json').read_bytes());u=next(x for x in inv['material_source_units']if x['key']=='primer-linalg.html::node-184');assert u==q['entire_current_literal']
owner=json.loads((R/'book/coverage/foundations.json').read_bytes());assert all(x in owner['material_claims']for x in q['entire_original_owner_rows'])
ls=(R/u['source']).read_text().splitlines(keepends=True);assert ''.join(ls[179:214])==q['full_current_context_lines180_to214']
refs=[Q,p]
for v in q['full_selected_sources_to_read']:refs.append(read(v))
trials=[]
for i,t in enumerate(q['actual_three_trials_failure_failure_pass']):
 a=read(t['actual']);d=json.loads(a.read_bytes());log=read(t['raw_log']);snap=read(t['source_snapshot']);refs +=[a,log,snap]
 assert d['actual_exit_code']==d['actual_runner_exit_code']==t['actual_exit_code']==[1,1,0][i]
 assert d['protection_errors']==[]and d['source_sha256_before']==d['source_sha256_after']==sha(snap)
 assert d['raw_log_sha256']==sha(log)and log.read_text().count('warning:')==t['warning_diagnostic_count']==[2,2,3][i]
 for k in ['started_at_utc','finished_at_utc','elapsed_seconds']:assert d[k]==t[k]
 assert d['actual_command']==['lake','env','lean',d['source']]and d['actual_workdir']==str(R/'verification/lean')
 trials.append(t)
assert trials[-1]['source_snapshot']['sha256']==q['proof_source']['sha256']
out={'status':'passed_independent_full_normcomparison8_entire_literal184_semantic_review','errors':[],'reviewer':'/root/modules_finish28','reader_started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':{'file':str(Q),'sha256':sha(Q)},'proof_source':q['proof_source'],'individual_full_literal_decisions':[{'source_unit_key':u['key'],'entire_literal_approved':True,'missing_clauses':[],'full_clause_reason':'Every coordinate square is genuinely bounded by the finite sum; the displayed squared l1 sum is expanded into the full nonnegative double sum and bounded below by the squared l2 sum. A largest squared coordinate is an actual attained index under Nonempty I, and the full sum is bounded by dimension times its square through the true Pi infinity norm. The exact Euclidean pairing of |x| with ones, norm of ones sqrt(cardI), and real Cauchy-Schwarz prove the printed third route. All generic norm inequalities use actual distinct l1/l2/Pi infinity norms, including empty-coordinate zero inequalities without asserting an empty maximum. The actual printed vector[3,-4,12] has norms12/13/19 and squared sums169/361;12≤13≤19≤13sqrt3 and the strict nearest-tenth enclosure about22.5 are genuine. The separate surrounding Fact tightness and ball/certificate/infinite-dimensional clauses are excluded.'}],'all_eight_full_bodies_definition_and_three_selected_sources_read':True,'used_primary_API_scope':'Previously full-read real InnerProductSpace Basic and finite PiL2 construction/norm/inner formulas; actual Finset.single_le_sum, norm_le_pi_norm and finite maximum source bodies used by complete selected NormDuality and NormExercises read.','three_original_native_bodies_times_and_failures_preserved':trials,'actual_warning_counts':[2,2,3],'author_message_two_two_two_not_adopted':'Actual request and raw final log contain3warnings; native exact warnings retained without suppression.','no_compiler_live_source_owner_selection_canonical_publication_change':True,'coverage_complete':False,'original_read_refs':[{'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}for p in dict.fromkeys(refs)]}
O.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'whole184':True,'actual_warnings':[2,2,3],'peer_sha256':sha(O)}))
