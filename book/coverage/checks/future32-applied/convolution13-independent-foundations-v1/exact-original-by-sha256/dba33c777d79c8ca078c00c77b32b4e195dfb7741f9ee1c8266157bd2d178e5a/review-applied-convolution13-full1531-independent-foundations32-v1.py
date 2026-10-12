from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');Q=R/'book/coverage/checks/future31-applied/convolution13-author-components-v2/convolution13-entire-source-all-bodies-current1531-entire-literal-independent-review-request31-v1.json';O=Path('/tmp/applied-convolution13-full-current1531-independent-foundations32-findings-v1.json');assert not O.exists()
def path(n):return Path(n)if Path(n).is_absolute()else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def checked(r):
 p=path(r['file']);assert sha(p)==r['sha256']
 if 'bytes'in r:assert p.stat().st_size==r['bytes']
 return p
assert sha(Q)=='e6e8709782efa6d2bc7228b97b46a466428d7a4923b70133ba474f2c71891d80';q=json.loads(Q.read_bytes())
aliases=q['all_original_byte_aliases']
for a in aliases.values():checked(a.get('original_byte_copy',a.get('already_durable_exact_reference')))
source=checked(q['reviewed_source']);s=source.read_text();sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations,without_comments
assert declarations(s)==q['all_public_declarations']and len(declarations(s))==q['public_name_count']==20
assert len([x for x in declarations(s)if x['kind']=='theorem'])==q['public_theorem_count']==13
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',without_comments(s))
assess=[
'Finite tap reversal is an involution using genuine Fin.rev_rev; no convolution identity is assumed.',
'The actual reverse index has integer value k-1-j. The Fin0 case is vacuous rather than assuming a nonexistent tap.',
'An actual Fin.revPerm finite sum bijection converts independently defined negative tap offsets to positive offsets of reversed taps, with the exact right-edge shift d*(k-1). Empty tap sums are also valid.',
'The reverse correlation identity follows by genuine reversal involution, on every integer signal/kernel/dilation/start.',
'Integer stride/start-padding offsets and an arbitrary real bias preserve the proven identity pointwise. The unused b binder contributes the real diagnostic, and is not a mathematical assumption.',
'Forward and backward valid-window indices are equal after tap reversal by actual Fin value arithmetic; the bounds guarantee every index is inside the input.',
'Reindexing the genuine finite valid-window convolution sum yields correlation with reversed weights for all finite inputs and all n+1 output positions, with k+1 nonempty taps.',
'Involution gives the finite valid-window reverse identity on the same input/output domains.',
'The identical w vector at every output defines true parameter sharing, and the actual Fintype cardinalities derive the stated input/output dimensions.',
'The exact printed kernel(1,-1) reverses to(-1,1) by checking both actual finite tap positions.',
'For every real four-vector, actual correlation equals the supplied actual3x4 matrix product; the selected matrix proof is genuine entrywise multiplication.',
'For every real four-vector, the same negative-offset kernel yields positive neighboring differences, while its actual reversal yields the original matrix/correlation map.',
'The exact input(1,2,3,4) gives correlation(-1,-1,-1), convolution(1,1,1), reversed convolution(-1,-1,-1), with three outputs and four inputs. Thus the convention distinction is substantive.'
]
starts=list(re.finditer(r'^theorem (\w+)',s,re.M));assert len(starts)==13;body=[]
for i,m in enumerate(starts):
 tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|def|end |section |namespace )',tail[1:]);b=tail[:stop.start()+1]if stop else tail
 body.append({'declaration':'SafeLearning.CompleteAppliedConvolutionReversalBridge31.'+m.group(1),'complete_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'exact_all_input_predicates_and_conclusion':b.split(':=',1)[0].strip(),'entire_body_read':True,'exact_component_approved':True,'independent_assessment':assess[i]})
natives=[]
for h in q['all_genuine_native_histories']:
 n=json.loads(checked(h['actual_native']).read_bytes());raw=checked(h['raw_log']);snap=checked(h['source_snapshot'])
 assert n['actual_exit_code']==h['actual_exit_code']==0 and n['protection_errors']==[]and n['source_unchanged']is True
 assert n['source_sha256_before']==n['source_sha256_after']==sha(snap)and n['raw_log_sha256']==sha(raw)
 assert n['actual_command']==['lake','env','lean',n['source']]and n['actual_workdir']==str(R/'verification/lean')
 assert all(n[k]==h[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds'])
 headers=len(re.findall(r'^[^\n]+:\d+:\d+: warning:',raw.read_text(),re.M));occurrences=raw.read_text().count('warning:')
 assert headers==1 and h['warning_count']==occurrences==2
 natives.append({'exact_original_native':h['actual_native'],'source_snapshot':h['source_snapshot'],'raw_log':h['raw_log'],'original_body_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},'actual_emitted_location_first_warning_headers':headers,'original_author_warning_count_field_preserved':h['warning_count'],'actual_warning_colon_substrings_including_hint':occurrences,'warning_metadata_observation':'Original warning_count2 agrees with both warning-colon occurrences, one of which is the linter hint. The emitted diagnostic-header count is1; original field/native/source/raw/time not rewritten.'})
assert checked(q['actual_final_source_native']).read_bytes()==checked(q['all_genuine_native_histories'][0]['actual_native']).read_bytes()
assert checked(q['all_genuine_native_histories'][0]['source_snapshot']).read_bytes()==source.read_bytes()
axraw=checked(q['all_genuine_native_histories'][1]['raw_log']).read_text();ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",axraw,re.S)
assert len(ax)==13 and [n for n,_ in ax]==[b['declaration']for b in body]
assert all(set(x.strip()for x in raw.replace('\n',' ').split(','))<={'propext','Classical.choice','Quot.sound'}for _,raw in ax)
inv=json.loads(path('book/coverage/inventory-after-correction81.json').read_bytes());unit=next(x for x in inv['material_source_units']if x['key']=='primer-rl-nn.html::node-1531');assert unit==q['exact_current_unit']
current=path('SafeLearning/primer-rl-nn.html');assert sha(current)==unit['source_sha256'];arch=checked(aliases['SafeLearning/primer-rl-nn.html']['original_byte_copy']);assert current.read_bytes()==arch.read_bytes()
context=json.loads(checked(q['entire_local_context']).read_bytes());assert context['exact_current_unit']==unit
assert context['entire_exercise22_html']in current.read_text()and context['architecture_definition_and_example_html']in current.read_text()
ownerref=aliases['book/coverage/applied.json']['already_durable_exact_reference'];owner=json.loads(checked(ownerref).read_bytes());assert checked(ownerref).read_bytes()==path('book/coverage/applied.json').read_bytes()
assert all(r in owner['material_claims']for r in q['current_owner31_material_claims_for1531'])
additional=[ref('/home/oxrexkevin/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Data/Fin/Basic.lean'),ref('/home/oxrexkevin/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Init/Data/Fin/Lemmas.lean')]
assert path('verification/lean/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.1'
d={'status':'passed_independent_complete_convolution13_source_and_current1531_entire_literal_review','errors':[],'reviewer':'/root/foundations_recovery28','request':ref(Q),'entire_source':q['reviewed_source'],'all13_complete_body_assessments':body,'all7_actual_independent_definition_bodies_read':True,'all20_public_names':q['all_public_declarations'],'entire_current_literal':unit,'whole_current_literal_decision':{'approved':True,'remaining_mathematical_gaps':[],'all_parameter_sharing_reversal_convention_and_dimensions_clauses_approved':True},'entire_exercise22_and_full_convolution_definition_example_context_read':q['entire_local_context'],'both_entire_selected_sources_and_full_used_primary_Fin_rev_sum_reindexing_bodies_read':True,'additional_complete_actual_Lean4_34_1_Fin_rev_providers':additional,'all_original_genuine_source_and_axiom_histories':natives,'standard_axioms_per_public_theorem':{name:[x.strip()for x in raw.replace('\n',' ').split(',')]for name,raw in ax},'original_compiler_codes_and_warning_fields_body_times_preserved':True,'immutable_actual_installed_owner31_reference':ownerref,'original_pending1531_rows_unchanged':q['current_owner31_material_claims_for1531'],'independent_index_domain_assessment':'Positive-offset cross-correlation and negative-offset convolution are separate actual finite sums. The bridge includes the genuine right-edge translation d*(tapcount-1), and valid finite convolution uses i+k rather than wrongly aligning the left edge. Arbitrary real taps/inputs and integer stride/dilation/bias specialize to the physical example; no kernel-symmetry or desired-output premise is assumed. Parameter sharing is one identical kernel at every output. The current literal only claims this convention bridge and3-from4 dimensions.','no_parent_exercise_general_padding_multichannel_output_formula_or_architecture_whole_promoted':True,'no_current_source_owner_canonical_selected_or_publication_mutation':True,'coverage_complete':False}
O.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'status':'passed','errors':[],'public_theorems':13,'whole_current1531':True,'actual_emitted_warning_headers':[x['actual_emitted_location_first_warning_headers']for x in natives]}))
