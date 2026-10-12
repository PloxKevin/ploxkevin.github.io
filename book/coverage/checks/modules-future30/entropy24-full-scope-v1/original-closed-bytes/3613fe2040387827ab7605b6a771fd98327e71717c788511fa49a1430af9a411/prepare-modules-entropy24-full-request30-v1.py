from pathlib import Path
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/modules-future30/entropy24-full-scope-v1'
assert not B.exists();B.mkdir(parents=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
aliases={}
def copy(p):
 p=Path(p);h=sha(p);q=B/'original-closed-bytes'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():
  with q.open('xb') as f:f.write(p.read_bytes())
 assert sha(q)==h
 r={'file':q.relative_to(R).as_posix(),'sha256':h,'bytes':q.stat().st_size};aliases[str(p)]=r;return r
S=Path('/tmp/CompleteModulesViabilityEntropyWhole30-draft-v5.lean')
assert sha(S)=='405ccc0b2782c7520da92f330debbe11f17b5572ba08a5a8ea527b3ad806cedb'
t=S.read_text();ns='SafeLearning.CompleteModulesViabilityEntropyWhole30'
names=re.findall(r'^theorem\s+(\w+)',t,re.M);defs=re.findall(r'^def\s+(\w+)',t,re.M)
assert (len(names),len(defs))==(24,7)
invpath=R/'book/coverage/inventory-after-correction65.json';I=json.loads(invpath.read_bytes())
assert sha(invpath)=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
ownerpath=R/'book/coverage/checks/modules-future29/current65-pair-bound-v7/modules29-current65-two-source-pair-bound-candidate-v1.json'
assert sha(ownerpath)==sha(R/'book/coverage/modules.json')=='13a1955d1920b9eafec20b5b38d7e10800354db71188c154f0967a93bccbc22d'
M=json.loads(ownerpath.read_bytes());exkey='viability.html::exercise-20';keys=['viability.html::node-'+str(n) for n in [1167,1171,1173,1174]]
e=next(r for r in M['exercises'] if r['inventory_key']==exkey);assert e['status']=='pending' and len(e['claims'])==3
rows=[next(r for r in I['material_source_units'] if r['key']==k) for k in keys]
affected=[r for r in M['material_claims'] if set(r.get('source_unit_keys',[]))&set(keys)];assert len(affected)==4 and all(r['status']=='pending' for r in affected)
page=R/'SafeLearning/viability.html';assert sha(page)==e['source_sha256']=='0b0a8a5710cd4ce278e30c1c7a5534ba5f4388c7956d60a1e701c02b572490c0'
P=Path('/tmp/modules-entropy-penalty-precision-unnumbered-proposal30-v2/modules-entropy-penalty-precision-unnumbered-full29-proposal30-v2.json')
assert sha(P)=='3955d459841fd598064c71d35d7fda0d5eb162ae2f55a6443ea08f947cdfb6eb';p=json.loads(P.read_bytes())
assert p['fresh_changed_literal_keys']=={'exercises':[exkey],'material_source_units':[keys[-1]]}
for v in p.values():
 if isinstance(v,dict) and {'file','sha256'}<=v.keys():
  z=Path(v['file']);z=z if z.is_absolute() else R/z;assert sha(z)==v['sha256'];copy(z)
for j in [1,2]:
 pn=Path('/tmp/modules-entropy-penalty-precision-unnumbered-proposal30-preparation-actual-v'+str(j)+'.json');a=json.loads(pn.read_bytes());assert a['actual_exit_code']==0 and a['protection_errors']==[]
 for z in [pn,a['raw_log'],'/tmp/prepare-modules-entropy-penalty-precision-unnumbered-proposal30-v'+str(j)+'.py','/tmp/run-modules-entropy-penalty-precision-unnumbered-proposal30-preparation-v'+str(j)+'.py']:copy(z)
context={'entire_current_entropy_exercise_context_lines958_972':''.join(page.read_text().splitlines(keepends=True)[957:972]),
 'entire_current_exercise_inventory_row':next(r for r in I['exercises'] if r['key']==exkey),
 'entire_original_pending_exercise_owner_row':e,'four_entire_current_material_inventory_rows':rows,'four_entire_old_pending_material_claim_rows':affected,
 'entire_prospective_corrected_exercise_literal':p['entire_current_and_proposed_literal_records'][exkey]['entire_proposed'],
 'entire_prospective_corrected_node1174_literal':p['entire_current_and_proposed_literal_records'][keys[-1]]['entire_proposed'],
 'entire_current_entropy_Section5_context_lines480_539':''.join(page.read_text().splitlines(keepends=True)[479:539]),
 'entire_actual_two_sided_Q_and_delta_threshold_walkthrough_JS_lines1054_1086':''.join(page.read_text().splitlines(keepends=True)[1053:1086])}
C=B/'modules-entropy24-full-current-and-prospective-context-v1.json';C.write_text(json.dumps(context,indent=2,ensure_ascii=False)+'\n')
history=[]
for j in range(1,6):
 z=Path('/tmp/modules-viability-entropy-whole30-owner29-trial'+str(j)+'.json');n=json.loads(z.read_bytes())
 assert n['actual_exit_code']==[1,1,0,0,0][j-1] and n['protection_errors']==[] and n['source_unchanged']
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']==sha(n['source_snapshot'])
 assert sha(n['raw_log'])==n['raw_log_sha256'];raw=Path(n['raw_log']).read_text()
 wc=len(re.findall(r'^.*?:\d+:\d+: warning:',raw,re.M));assert wc==[8,7,12,14,14][j-1]
 history.append({'actual_native':copy(z),'actual_source':copy(n['source']),'actual_source_snapshot':copy(n['source_snapshot']),
  'actual_raw_log':copy(n['raw_log']),'actual_exit_code':n['actual_exit_code'],'actual_warning_count':wc,
  'original_times':{k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'original_body_and_times_untouched':True})
end=b'end SafeLearning.CompleteModulesViabilityEntropyWhole30\n'
prefix=[]
for k in [3,4]:
 old=Path('/tmp/CompleteModulesViabilityEntropyWhole30-draft-v'+str(k)+'.lean').read_bytes()
 assert old.endswith(end) and S.read_bytes().startswith(old[:-len(end)])
 prefix.append({'original':copy('/tmp/CompleteModulesViabilityEntropyWhole30-draft-v'+str(k)+'.lean'),'preserved_exact_bytes_through_last_original_theorem':len(old)-len(end),'only_closing_namespace_end_moved_for_append':True})
selected=[copy(R/'verification/lean/SafeLearning'/(name+'.lean')) for name in ['CompleteAppliedTemperatureSoftmax','CompleteAppliedFiniteEntropy','CompleteAppliedInformation','CompleteAppliedFiniteKLSupport','CompleteAppliedFiniteKL','CompleteFoundationsExponentialLesson']]
primary=[]
for name in ['Probability/Distributions/Uniform.lean','Probability/ProbabilityMassFunction/Basic.lean','MeasureTheory/Measure/Typeclasses/Probability.lean','MeasureTheory/OuterMeasure/Basic.lean','InformationTheory/KullbackLeibler/Basic.lean','Analysis/Complex/ExponentialBounds.lean','Analysis/SpecialFunctions/Log/Basic.lean']:
 z=R/'verification/lean/.lake/packages/mathlib/Mathlib'/name
 primary.append({'original_external_package_path_historical_metadata':str(z),'exact_physical_byte_alias':copy(z)})
for z in ['/tmp/root_tmp_lean_current65_owner29_context_v1.json','/tmp/root_tmp_lean_current65_owner29_runner_v1.py',__file__,'/tmp/run-modules-entropy24-full-request30-preparation-v1.py']:copy(z)
paperdir=Path('/tmp/modules-entropy2506-primary30-v1');receipt=json.loads((paperdir/'actual-primary-download-receipt-v1.json').read_bytes())
assert receipt['actual_http_status']==200 and receipt['bytes']==1538134 and sha(paperdir/'massiani-2506.10871v1.pdf')==receipt['sha256']=='29e15b2eb69c63ec55606fd8312f830e9502d70e4888a1a19eadf6091247185a'
paper=[copy(paperdir/name) for name in ['massiani-2506.10871v1.pdf','massiani-2506.10871v1.txt','actual-primary-download-receipt-v1.json']]
d={'status':'prepared_actual_passed_entropy24_full_source_and_literals_for_independent_semantic_review_only',
 'source':copy(S),'source_sha256':sha(S),'public_theorem_count':24,'public_definition_count':7,'public_declaration_count':31,
 'public_theorem_names':[ns+'.'+n for n in names],'public_definition_names':[ns+'.'+n for n in defs],
 'exercise_keys':[exkey],'material_unit_keys':keys,'entire_current_and_prospective_context':copy(C),'current_page_original_byte_alias':copy(page),
 'original_owner29_candidate':{'file':ownerpath.relative_to(R).as_posix(),'sha256':sha(ownerpath)},
 'current_inventory':copy(invpath),'genuine_lean_native_history':history,'earlier_passed_proof_body_prefixes':prefix,
 'selected_complete_dependency_sources':selected,'primary_used_API_full_sources':primary,
 'actual_primary_entropy_paper_original_bytes':paper,'primary_url':'https://arxiv.org/pdf/2506.10871v1',
 'primary_paper_used_scope':'Full sections3.2,5.1,6.1.2/Fig3 and AppendixD.3 Lemma2 and proof ofTheorem2 read. No general theorem2/closeness/robustness-optimizer convergence or whole Section5 promotion is requested.',
 'unnumbered_narrow_wording_proposal':copy(P),'actual_narrow_wording_author_parser':copy('/tmp/modules-entropy-penalty-precision-unnumbered-proposal30-preparation-actual-v2.json'),
 'full_scope_review_requests':[
  {'scope':'current entire Exercise7.6 and current node1174','whole_scope_expected_pending':True,
   'remaining_gap':'The printed -ln(10^-2)=4.605 and the two p1 decimal equations are approximate rather than exact;13.30 is slightly below the true sufficient threshold. The direct sufficient-bound calculation supports its growth, while fixed-penalty degradation is an empirical cliff-world attribution.'},
  {'scope':'prospective corrected entire Exercise7.6 and corrected node1174 conditional on actual later source application',
   'conclusions':['Actual all-time safe stochastic paths on an arbitrary probability space yield a genuine viability witness. Deterministic-path kernel equals existence of an actual stationary deterministic safe controller, matching the positive-time source convention for nonterminal failure.',
    'Actual measurable first action is pushed forward from its true probability measure to a finite PMF. If its successor is unviable, every realized trajectory in that first-action event hits failure at some later positive time. A true countable union of zero-probability failure events gives mass0 for every unviable first action, deriving support in the actual viable slice.',
    'A genuine supported PMF has a nonempty viable slice. PMF.uniformOfFinset gives exact reciprocal-cardinality masses. Its actual KL divergence equals log(card)-Shannon entropy; genuine nonnegativity gives the cap, and genuine Gibbs equality proves equality iff uniform.',
    'Actual normalized exponential PMF denominator is bounded below by one viable action mass. The displayed two-sided Q bounds derive the full exponential critical-action probability bound, whose exact equivalence to the p1 threshold is proved. p>=p1 suffices for the source per-action delta-safety convention.',
    'Actual illustrative exact thresholds are11+ln10 and14+4ln10. One extra decade costs exactly alpha ln10/u3. Real.log2/log5 rigorous rational enclosures prove the original4.605/13.30/23.21/1.15/4.61 rounding intervals, and a genuine non-equality proves4.605 is not exact.',
    'The exact illustrative sufficient threshold is10+(2+2ln10)alpha and exceeds any fixed real penalty at some positive temperature. No actual problem-unsafety conclusion is inferred from this conservative bound; the directly read primary cliff-world example supplies its attributed empirical competition.']},
  {'scope':'current nodes1167/1171/1173','entire_current_literal_review_requested':True,
   'conclusions':['Question1167 is answered by the true safe-process support/entropy theorem and the exact numerical thresholds/decade increments. Answer1171 and KL explanation1173 are directly proved with actual probability laws and actual cardinality-supported entropy.']}],
 'domain_scope':['Finite nonempty action set Fin m. Kernel witness/actual safe-path arguments work for arbitrary state types, hence include the finite source spaces.','Safe events are zero-probability visits at every positive discrete time; initial failure is not automatically excluded, matching the printed nonterminal source convention. The first action is genuinely measurable on an arbitrary probability space.','Entropy bound and uniform equality concern the displayed viable-slice distribution. No uniform viable law is asserted to define a globally safe stationary controller in a nonterminal recoverable failure convention.','The softmax threshold assumes exactly the displayed two-sided Q bounds and positive alpha,u3,delta; it derives the desired probability bound from normalized masses. Constants are the exercise illustrative constants, not empirical paper values.'],
 'original_closed_byte_aliases':aliases,'required_evidence_artifacts_sha256':{r['file']:r['sha256'] for r in aliases.values()},
 'source_number_reserved':False,'source_applied':False,'canonical_pairs_executed':False,'whole_promotion_performed':False,
 'independent_full_semantic_review_pending':True,'coverage_complete':False,'supplementary_after_frozen29_manifest':True}
d['required_evidence_artifacts_sha256'][d['original_owner29_candidate']['file']]=d['original_owner29_candidate']['sha256']
O=B/'modules-entropy24-full-source-literal-independent-review-request30-v1.json';O.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'request':O.relative_to(R).as_posix(),'sha256':sha(O),'bytes':O.stat().st_size,'closed_refs':len(d['required_evidence_artifacts_sha256']),'aliases':len(aliases),'warning_counts':[x['actual_warning_count'] for x in history]}))
