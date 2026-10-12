from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased')
REQ=R/'book/coverage/checks/modules-future29/leaky-qc30-and-source63-v1/modules-leaky-qc30-full-scope-independent-review-request29-v1.json'
CTX=Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(p):p=Path(p);return p if p.is_absolute() else R/p
def ref(p):p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
ctx=json.loads(CTX.read_bytes());pins={**ctx['pins_sha256'],**ctx['held_current_source_sha256']}
def guard():
 for p,h in pins.items():assert sha(R/p)==h,p
before={p:sha(R/p) for p in pins};guard()
assert sha(REQ)=='c61c3f41530e338adadb50f5739771b344f488886fb2700ae83d583cb7545c18'
d=json.loads(REQ.read_bytes());closed={str(REQ):sha(REQ),str(CTX):sha(CTX),str(Path(__file__)):sha(__file__)}
def add(q):
 p=path(q['file']) if isinstance(q,dict) else path(q)
 if isinstance(q,dict):assert sha(p)==q['sha256'],str(p)
 closed[str(p)]=sha(p);return p
for p,h in d['required_evidence_artifacts_sha256'].items():
 p=path(p);assert p.resolve().is_relative_to(R) and sha(p)==h,str(p);closed[str(p)]=h
for original,q in d['original_exact_byte_aliases'].items():
 a=add(q);assert a.resolve().is_relative_to(R)
 o=path(original)
 if o.exists():assert sha(o)==sha(a),original
s=add(d['proof_source']).read_text();assert s==d['entire_final_proof_source']
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s)
ns='SafeLearning.CompleteModulesLeakyReLUQC28.'
assert [ns+x for x in re.findall(r'^theorem\s+(\w+)',s,re.M)]==d['public_theorem_names'] and len(d['public_theorem_names'])==30
old=Path('/tmp/CompleteModulesLeakyReLUQC28-draft-v7.lean');add(old)
assert s.startswith(old.read_text().rsplit('end SafeLearning.',1)[0])
assert s.endswith('end SafeLearning.CompleteModulesLeakyReLUQC28\n')
warningcounts=[]
for trial,expected in zip(d['actual_six_native_trials_preserved'],[1,1,1,0,1,0]):
 native=add(trial['actual']);log=add(trial['raw_log']);snap=add(trial['original_source_snapshot']);n=json.loads(native.read_bytes())
 assert type(n['actual_exit_code']) is int and n['actual_exit_code']==expected==trial['actual_lean_exit_code']
 assert n['protection_errors']==[] and n['source_unchanged'] is True
 assert n['actual_workdir']==str(R/'verification/lean') and n['actual_command']==['lake','env','lean',n['source']]
 assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(snap)
 assert n['raw_log_sha256']==sha(log) and n['raw_log']==str(log) and n['source_snapshot']==str(snap)
 assert n['finished_at_utc']>=n['started_at_utc']
 warningcounts.append(len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M)))
assert warningcounts==[0,0,0,0,0,0]
assert d['actual_six_native_trials_preserved'][-1]['original_source_snapshot']['sha256']==d['proof_source']['sha256']
assert add(d['actual_six_native_trials_preserved'][-1]['raw_log']).read_bytes()==b''
for q in d['full_selected_dependency']+d['used_primary_complete_source_refs']:add(q)
base=json.loads((R/'book/coverage/inventory.json').read_bytes());em={r['key']:r for r in base['exercises']};mm={r['key']:r for r in base['material_source_units']}
assert d['entire_current_exercise']==em['lipsdp.html::exercise-16']
for row in d['entire_current_five_material_units']:assert row==mm[row['key']]
source=(R/'SafeLearning/lipsdp.html').read_text()
assert d['full_current_exercise_context'] in source and d['full_unchanged_section6_context'] in source
for key,pair in d['entire_prospective_exercise_and_node1293'].items():
 current=em[key] if key in em else mm[key];assert pair['entire_current']==current
 proposed=pair['entire_proposed'];a=current['source_text'];b=proposed['source_text']
 assert a.count('is no longer convex')==1 and a.replace('is no longer convex','need not be convex')==b
 assert hashlib.sha256(b.encode()).hexdigest()==proposed['text_sha256']
 for k,v in current.items():
  if k not in ['source_text','text_sha256','source_sha256']:assert proposed[k]==v
assert d['current_source63_not_applied'] is True and d['current_whole_exercise_and_node1293_approval_requested'] is False
assert d['full_current_exercise_context'].replace('is no longer convex','need not be convex')==d['full_proposed_exercise_context']
add(d['prospective_source63_proposal'])
for q in d['original_files_to_close']:add(q)
guard();assert before=={p:sha(R/p) for p in pins}
prospective=d['entire_prospective_exercise_and_node1293']
groups=[
 {'part':'a','approved':True,'hypotheses':['0<a<1','distinct endpoints for chord division; oriented interval integral handles either order'],'reason':'The actual max activation is continuous, has the printed negative/positive slopes, and an integrable right-derivative representative. One-sided FTC plus equality to genuine deriv almost everywhere derives the literal chord-average identity and sector bounds; no differentiability at zero is assumed.'},
 {'part':'b','approved':True,'hypotheses':['0<a<1; generic product equivalence needs a<1'],'reason':'The generic interval/product equivalence, exact scalar matrix expansion, and actual nonnegative QC cover the displayed derivation. Equal endpoints have zero QC and are handled without division.'},
 {'part':'c','approved':True,'hypotheses':['0<a<1','endpoint-slope equality statement for distinct inputs; identical inputs handled separately'],'reason':'Actual a=1/10,2,-1 gives difference3,21/10,slope7/10 and QC81/25. The common closed-halfline characterization includes zero endpoints, and strict opposite-sign pairs have strictly positive QC.'},
 {'part':'d','approved':True,'hypotheses':['fixed PSD multiplier T','nonnegative lower and upper slope coefficients','prospective need-not-be-convex wording'],'reason':'The finite-dimensional negative-Gram PSD deficit proves matrix concavity. A fixed positive multiplier and positive prescribed bound have two feasible endpoints with an excluded midpoint, so nonconvexity is genuinely witnessed. Exact convex exceptions forbid a universal reading. Alpha zero removes the negative-Gram term, leaves a valid incremental QC, and is strictly conservative on negative leaky chords. The primary fixed-T/Schur rationale is directly checked.'}
]
units=[{'key':r['key'],'entire_source_record':r,'whole_unit_approved':r['key']!='lipsdp.html::node-1293','missing_clauses':[] if r['key']!='lipsdp.html::node-1293' else ['The current universal no-longer-convex wording is false; only the prospective Source63 need-not qualifier is approved.']} for r in d['entire_current_five_material_units']]
out=Path('/tmp/leakyqc30-independent-applied-findings29-v1.json');assert not out.exists()
out.write_text(json.dumps({'status':'passed_independent_full_leakyqc30_source_and_prospective_source63_semantic_review','reviewer':'/root/applied_next','review_completed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQ),'proof_source':d['proof_source'],'all30_public_and_private_definitions_full_bodies_read':True,'full_selected_Modules_source_read':d['full_selected_dependency'],'used_primary_complete_refs_rehashed_and_used_API_statements_bodies_read':d['used_primary_complete_source_refs'],'primary_paper_direct_read':{'url':'https://arxiv.org/pdf/2005.02929','observed_version':'arXiv2005.02929v2,15Sep2020','locators':'SectionIII.A eq7 and Remarks3/4,PDFpage3','own_observation':'For fixed T the primary sets alpha zero and applies a Schur complement to obtain an LMI affine in squared bound and weights; it identifies conservatism and displays the one-hidden-layer three-block matrix.'},'components':groups,'current_exercise':{'key':'lipsdp.html::exercise-16','whole_exercise_approved':False,'missing_clauses':['Current part(d) universal nonconvexity wording; prospective Source63 narrows it.']},'material_units':units,'prospective_source63_exercise':{'key':'lipsdp.html::exercise-16','entire_source_record':prospective['lipsdp.html::exercise-16']['entire_proposed'],'whole_exercise_approved':True,'missing_clauses':[],'source_application_and_canonical_pair_pending':True},'prospective_source63_node1293':{'entire_source_record':prospective['lipsdp.html::node-1293']['entire_proposed'],'whole_unit_approved':True,'missing_clauses':[],'source_application_pending':True},'old28_source_preservation_precise':'Entire old v7 source through its final theorem is an exact byte prefix; its closing namespace terminator is moved after the two added theorems. Full old source remains unchanged separately.','all_six_original_native_bodies_times_and_failures_preserved':True,'actual_lean_exit_codes':[1,1,1,0,1,0],'actual_warning_header_counts':warningcounts,'no_current_or_live_whole_promotion_or_compiler_rerun':True,'closed_evidence_sha256':closed,'errors':[]},ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(out),'all_guards_passed':True,'physical_durable_request_refs':len(d['required_evidence_artifacts_sha256']),'current_units_approved':4,'prospective_whole_and_node1293_approved':True}))
