from pathlib import Path
import contextlib,hashlib,importlib.util,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future31-applied/conditional28-author-components-v1/conditional28-full-source-current-and-prospective387-independent-review-request31-v1.json';B=Path('/tmp/applied-conditional28-independent-foundations32-v2');assert not B.exists()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert sha(p)==r['sha256']
 if 'bytes'in r:assert p.stat().st_size==r['bytes']
 return p
assert sha(Q)=='2e3270222d8b2b384cdf1d03dc2723d8e32f1691036862ecf9c57106494beae8';q=json.loads(Q.read_bytes())
for name,h in q['required_evidence_artifacts_sha256'].items():assert sha(name)==h
for r in q['full_file_original_byte_aliases'].values():checked(r)
source=checked(q['final_actual_passed_complete_source']);s=source.read_text();sys.path.insert(0,str(R/'book/coverage'));from lean_names import without_comments
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',without_comments(s))
public=list(re.finditer(r'^theorem (\w+)',s,re.M));assert len(public)==q['actual_public_theorem_count']==28
names=['SafeLearning.CompleteAppliedConditionalExpectationMaterial31.'+m.group(1)for m in public]
assessments=[]
for i,m in enumerate(public):
 tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|end |section |namespace |noncomputable def)',tail[1:]);body=tail[:stop.start()+1]if stop else tail
 a=q['all_complete_public_signatures'][i];assert a['declaration']==names[i]and a['actual_signature']==body.split(':=',1)[0].strip()and a['exact_source_block_sha256']==hashlib.sha256(body.encode()).hexdigest()
 assessments.append({**a,'entire_body_and_actual_all_input_predicates_read':True,'independently_approved_exact_component':True})
old=checked(q['all_two_old_genuine_compiler_histories'][-1]['source']).read_bytes()
assert source.read_bytes().startswith(b'import Mathlib\n'+old)
histories=q['all_two_old_genuine_compiler_histories']+q['all_six_new_genuine_compiler_histories'];codes=[];warnings=[]
for h in histories+[q['actual_separate_all28_axiom_native']]:
 n=json.loads(checked(h['native']).read_bytes());sp=checked(h['source']);snap=checked(h['source_snapshot']);raw=checked(h['raw_log'])
 assert n['actual_exit_code']==h['actual_exit_code']and n['protection_errors']==[]and n['source_unchanged']is True
 assert n['source_sha256_before']==n['source_sha256_after']==sha(sp)==sha(snap)and sp.read_bytes()==snap.read_bytes()
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')and n['raw_log_sha256']==sha(raw)
 assert all(n[k]==h['original_body_times'][k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds'])
 wc=len(re.findall(r'^[^\n]+:\d+:\d+: warning:',raw.read_text(),re.M));assert wc==h['actual_warning_headers']
 codes.append(n['actual_exit_code']);warnings.append(wc)
assert codes[:8]==[1,0,1,1,1,1,1,0]and codes[-1]==0
assert histories[-1]['source']['sha256']==q['final_actual_passed_complete_source']['sha256']
axraw=checked(q['actual_separate_all28_axiom_native']['raw_log']).read_text();axpairs=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",axraw,re.S)
assert len(axpairs)==28 and [name for name,_ in axpairs]==names
assert all(set(x.strip()for x in raw.replace('\n',' ').split(','))<={'propext','Classical.choice','Quot.sound'}for _,raw in axpairs)
for r in q['complete_direct_used_primary_source_texts'].values():checked(r)
additional=ref('verification/lean/.lake/packages/mathlib/Mathlib/Probability/Distributions/Bernoulli.lean')
proposal=json.loads(checked(q['two_exact_offline_qualifier_proposal']).read_bytes());alias=q['full_file_original_byte_aliases'];original=checked(alias[proposal['source']]);candidate=checked(alias[proposal['candidate']]);current=path('SafeLearning/primer-probability.html')
assert original.read_bytes()==current.read_bytes()and sha(current)==proposal['source_sha256']=='eeb3a23fe5a574b25e1e2e82adc149c51a8dcfadebf57ee4fa7b8d5f7ca13ea0'
oldtext=original.read_text();newtext=oldtext
for r in proposal['exact_replacements']:assert newtext.count(r['before'])==1 and r['after']not in newtext;newtext=newtext.replace(r['before'],r['after'],1)
assert newtext.encode()==candidate.read_bytes()and sha(candidate)==proposal['candidate_sha256']
inverse=newtext
for r in reversed(proposal['exact_replacements']):assert inverse.count(r['after'])==1;inverse=inverse.replace(r['after'],r['before'],1)
assert inverse.encode()==original.read_bytes()
sys.path.insert(0,str(R/'book'));from validate import Document
assert [(x.tag,x.attrs,x.line)for x in Document(oldtext).nodes]==[(x.tag,x.attrs,x.line)for x in Document(newtext).nodes]
B.mkdir();I=B/'isolated-full29-parser';(I/'SafeLearning').mkdir(parents=True)
for p in sorted((R/'SafeLearning').glob('*.html')):(I/'SafeLearning'/p.name).write_bytes(candidate.read_bytes()if p==current else p.read_bytes())
assert len(list((I/'SafeLearning').glob('*.html')))==29
H=R/'book/inventory_claims.py';spec=importlib.util.spec_from_file_location('conditional28_full_independent_fresh_bothROOTOUT',H);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.ROOT=I;m.OUT=I/'book/coverage';assert m.ROOT.resolve().is_relative_to(B)and m.OUT.resolve().is_relative_to(B)
stdout=B/'actual-independent-full29-parser-stdout.log'
with stdout.open('x')as f,contextlib.redirect_stdout(f):m.inventory()
a=json.loads(path('book/coverage/inventory-after-correction81.json').read_bytes());b=json.loads((m.OUT/'inventory.json').read_bytes());assert a['counts']==b['counts']and b['counts']['exercises']==556 and b['counts']['material_source_units']==12774
assert b['source_sha256']=={**a['source_sha256'],'SafeLearning/primer-probability.html':sha(candidate)}
changes={}
for field in ['exercises','material_source_units']:
 av={x['key']:x for x in a[field]};bv={x['key']:x for x in b[field]};assert av.keys()==bv.keys();changes[field]=[]
 for k in av:
  x=dict(av[k]);y=dict(bv[k])
  if x['source']=='SafeLearning/primer-probability.html':x.pop('source_sha256');y.pop('source_sha256')
  if x!=y:
   assert {n:v for n,v in x.items()if n not in ['source_text','text_sha256']}=={n:v for n,v in y.items()if n not in ['source_text','text_sha256']};changes[field].append(k)
assert changes=={'exercises':[],'material_source_units':['primer-probability.html::node-387']}
assert av['primer-probability.html::node-387']==q['entire_current387']and bv['primer-probability.html::node-387']==q['entire_prospective387']
manual={'original13':'Own full re-read confirms the observation sigma-algebra/factor measurability, integrable tower and known-event characterization, actual measurable pull-out with integrable product, nested tower and the real Bernoulli cost means 4.4/2.8/difference -1.6. These are exact components; no environment-wide performance lemma inferred.','L2_observation_and_MSE':'Doob-Dynkin factors the genuine strongly measurable conditional mean through Y. The actual orthogonal projection onto known L2 functions has orthogonal residual; Pythagoras yields the finite-risk mean-square inequality. Finite second moment is equivalent to L2 under AE measurability. The extended-risk proof first handles infinite competitor risk trivially, then derives competitor L2 from finite residual risk and X L2, without assuming finite competitor risk globally.','conditional_law':'The primary genuine conditional-distribution disintegration theorem identifies the conditional mean with the integral against a regular conditional real law. Integrability is derived for almost every observation under law(Y). Density identities use actual Radon-Nikodym/withDensity laws, with explicit density existence. Arbitrary measurable density versions are compared AE to the canonical density, then transported back along Y. No density for an atomic law or unique null-point value is asserted.','discrete_and_event':'Countable conditional mass sum follows from integrable atomic-kernel integral. The exact weighted tower handles null atoms separately and derives kernel integrability at each non-null observation, so both true marginal and joint mass sums equal the genuine expectation; no unjustified conditionally convergent rearrangement. Positive event means use the normalized restricted measure and true integral ratio/product identity.','whole_literal_conventions':'Random variables in the conditioning context are measurable; displayed random-variable equality is equality of conditional-expectation versions AE. The prospective first clause explicitly marks the AE observation version and law/density existence, and the second clause supplies integrability of X and measurable g with integrable product. These domain qualifications discharge all complete387 clauses; the old unrestricted each-y/integrability wording remains pending.'}
full={'status':'passed_full_independent_conditional28_components_current387_gaps_prospective387_whole_review','errors':[],'reviewer':'/root/foundations_recovery28','request':ref(Q),'entire_source':q['final_actual_passed_complete_source'],'all28_complete_public_body_assessments':assessments,'all_actual_definitions_and_private_L2_norm_square_body_read':True,'all_used_primary_bodies_read':q['complete_direct_used_primary_source_texts'],'additional_complete_used_Bernoulli_provider':additional,'independent_mathematical_assessment':manual,'all_original_eight_genuine_compiler_histories':histories,'actual_original_all28_axiom_native':q['actual_separate_all28_axiom_native'],'actual_standard_axioms_per_declaration':{name:[x.strip()for x in v.replace('\n',' ').split(',')]for name,v in axpairs},'actual_original_Lean_codes_preserved':codes,'actual_original_warning_headers_preserved':warnings,'current_whole_decision':{'entire_current_literal':q['entire_current387'],'approved':False,'remaining_gaps':['Unqualified conditional mean for each y disregards null-observation version freedom and conditional-law/density existence.','Integrable X and measurable g with integrable product are needed for the displayed expectation and pull-out interpretation.']},'prospective_whole_decision':{'entire_prospective_literal':q['entire_prospective387'],'approved':True,'remaining_gaps':[],'conditional_on_exact_later_source_application':True},'both_ROOT_and_OUT_independent_parser_isolated_TMP':True,'independent_parser_changed_keys':changes,'independent_full29_inventory':ref(m.OUT/'inventory.json'),'independent_parser_stdout':ref(stdout),'exact_proposal':q['two_exact_offline_qualifier_proposal'],'no_Source_ordinal_application_or_owner_or_canonical_or_selected_or_publication_mutations':True,'no_neighbor390_total_variance_performance_lemma_or_other_unit_promotion':True,'coverage_complete':False}
narrow={'status':'passed_independent_conditional387_two_exact_qualifiers_full_literal_support_and_fresh_full29_parser','errors':[],'reviewer':'/root/foundations_recovery28','request':ref(Q),'reviewed_exact_proposal':q['two_exact_offline_qualifier_proposal'],'exact_two_replacements':proposal['exact_replacements'],'current_full_source':ref(original),'proposed_full_source':ref(candidate),'entire_current_and_prospective387_read':True,'supporting_full28_math_review':ref(source),'full_domain_assessment':manual['whole_literal_conventions'],'both_parser_ROOT_and_OUT_strictly_TMP':True,'exact_full29_changed_keys':changes,'counts':b['counts'],'all_other28_pages_and_all_other_literal_records_unchanged':True,'DOMtags_attributes_lines_preserved':True,'exact_forward_inverse_original_full_page_bytes':True,'actual_independent_parser_inventory':ref(m.OUT/'inventory.json'),'actual_independent_parser_stdout':ref(stdout),'author_original_preparation_body_time_native_and_prior_v1_preserved':True,'source_ordinal_reserved_or_applied':False,'whole_current_source_or_owner_or_canonical_promotion':False,'coverage_complete':False}
full['genuine_original_reader1_prefix_assumption_failure']={'helper':ref('/tmp/review-applied-conditional28-whole-and-narrow-independent-foundations32-v1.py'),'wrapper':ref('/tmp/run-review-applied-conditional28-whole-and-narrow-independent-foundations32-v1.py'),'native':ref('/tmp/applied-conditional28-full-math-and-narrow-independent-foundations32-actual-v1.json'),'raw_log':ref('/tmp/applied-conditional28-full-math-and-narrow-independent-foundations32-actual-v1.log'),'diagnosis':'Old13 source starts at the explicit ConditionalExpectation.Basic import; final28 prepends one import Mathlib. Original source/math/native bytes unchanged.'}
F=B/'applied-conditional28-full-current-components-prospective387-whole-independent-foundations32-findings-v1.json';N=B/'applied-conditional387-two-qualifiers-full29-independent-foundations32-findings-v1.json';F.write_text(json.dumps(full,indent=2)+'\n');N.write_text(json.dumps(narrow,indent=2)+'\n');print(json.dumps({'status':'passed','errors':[],'public_theorems':28,'current_whole':False,'prospective_whole':True,'changed':changes,'histories':8}))
