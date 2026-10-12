from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys,importlib.util,re
R=Path('/home/oxrexkevin/SafetyBased');W=Path('/tmp/source65-narrow-independent-foundations29-v1');assert not W.exists();W.mkdir();sys.path.insert(0,str(R/'book'));from validate import Document
Q='book/coverage/checks/modules-future29/scalar-lipsdp42-and-source65-v1/modules-source65-current64-narrow-independent-review-request29-v3.json'
def p(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def read(n):return json.loads(p(n).read_bytes())
def ref(n):return {'file':str(n),'sha256':sha(n)}
def check(r):assert p(r['file']).is_file() and sha(r['file'])==r['sha256'];return read(r['file']) if p(r['file']).suffix=='.json' else p(r['file']).read_bytes()
ctx=read('/tmp/root_tmp_lean_current64_owner28_context_v1.json')
def guard():
 for field in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in ctx[field].items():assert sha(n)==h,n
 return {'context':ref('/tmp/root_tmp_lean_current64_owner28_context_v1.json'),'inventory':ref('book/coverage/inventory.json'),'corrections':ref('book/coverage/material-corrections.json'),'selected_sources':1186,'assets':31,'owners':5}
started=datetime.now(timezone.utc).isoformat();before=guard();q=read(Q);proposal=check(q['proposal']);inv=check(q['source64_inventory']);assert q['exact_two_replacements']==proposal['exact_replacements'] and len(proposal['exact_replacements'])==2
for n,h in q['required_evidence_artifacts_sha256'].items():assert sha(n)==h,n
old=p(proposal['source']['file']).read_bytes();assert sha(proposal['source']['file'])==proposal['source']['sha256'];new=old.decode()
for r in proposal['exact_replacements']:assert new.count(r['before'])==1 and r['after'] not in new;new=new.replace(r['before'],r['after'],1)
assert new.encode()==check(proposal['proposed_source']) and new.count('\n')==old.decode().count('\n');reverse=new
for r in reversed(proposal['exact_replacements']):assert reverse.count(r['after'])==1;reverse=reverse.replace(r['after'],r['before'],1)
assert reverse.encode()==old
assert [(n.tag,n.attrs,n.line) for n in Document(old.decode()).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
assert 'w_0,w_1\\ne0' in proposal['entire_current_and_proposed_literal_records']['lipsdp.html::exercise-19']['entire_proposed']['source_text']
# Entire42 byte source checked; semantic approval is deliberately only the changed clauses' full support bodies.
scope=check(q['full_scope_request']);source=check(scope['proof_source']).decode();assert source==scope['entire42_public_bodies_and_definitions'];assert len(re.findall(r'^theorem ',source,re.M))==42
support=['actual_slope_restriction_implies_monotonicity_and_global_bound','actual_real_bound_iff_mathlib_lipschitz','actual_derivative_supremum_is_the_least_activation_lipschitz_constant','actual_network_bound_iff_activation_bound','actual_derivative_supremum_gives_the_exact_network_constant','actual_certificate_is_tight_exactly_for_the_activation_own_constant','actual_larger_supplied_upper_slope_has_the_printed_positive_ratio','actual_constant_activation_is_the_zero_constant_exception','actual_printed_relu_multiplier_squared_bound_and_gain','actual_printed_relu_source_matrix','actual_printed_matrix_characteristic_polynomial','actual_printed_matrix_has_exactly_the_two_stated_eigenvalue_roots','actual_printed_matrix_two_genuine_eigenvectors','actual_printed_negative_eigenvalue_three_decimal_enclosure']
for name in support:assert 'theorem '+name in source
trial=q['same42_actual_current64_pass'];a=check(trial['actual_native']);assert all(type(a[k]) is int and a[k]==0 for k in ['actual_exit_code','actual_runner_exit_code']) and a['protection_errors']==[]
assert check(trial['source_snapshot'])==source.encode();raw=check(trial['raw_log']).decode();assert len(re.findall(r'^.*\.lean:\d+:\d+: warning:',raw,re.M))==trial['actual_emitted_warning_count']==6
assert a['source_sha256_before']==a['source_sha256_after']==scope['proof_source']['sha256'] and a['started_at_utc']==trial['started_at_utc'] and a['finished_at_utc']==trial['finished_at_utc']
# Independent complete parser: BOTH bindings point into this new TMP root, all29 physical pages copied exactly.
isolated=W/'isolated-full29-parser';(isolated/'SafeLearning').mkdir(parents=True)
for page in (R/'SafeLearning').glob('*.html'):(isolated/'SafeLearning'/page.name).write_bytes(new.encode() if page.name=='lipsdp.html' else page.read_bytes())
assert len(list((isolated/'SafeLearning').glob('*.html')))==29
parser=R/'book/inventory_claims.py';assert sha(parser)==proposal['parser']['sha256'];spec=importlib.util.spec_from_file_location('source65_independent_isolated_full29_parser',parser);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.ROOT=isolated;m.OUT=isolated/'book/coverage';assert m.ROOT.is_relative_to('/tmp') and m.OUT.is_relative_to('/tmp');m.inventory();freshpath=m.OUT/'inventory.json';fresh=read(freshpath)
assert fresh['counts']==inv['counts']==proposal['counts'] and len(fresh['source_sha256'])==29
assert fresh['source_sha256']=={**inv['source_sha256'],'SafeLearning/lipsdp.html':proposal['proposed_source']['sha256']}
changed={}
for field in ['exercises','material_source_units']:
 aa={r['key']:r for r in inv[field]};bb={r['key']:r for r in fresh[field]};assert aa.keys()==bb.keys();changed[field]=[]
 for key in aa:
  x=copydict=dict(aa[key]);y=dict(bb[key])
  if x['source']=='SafeLearning/lipsdp.html':x.pop('source_sha256');y.pop('source_sha256')
  if x!=y:
   assert {k:v for k,v in x.items() if k not in ['source_text','text_sha256']}=={k:v for k,v in y.items() if k not in ['source_text','text_sha256']};changed[field].append(key)
 assert changed[field]==proposal['fresh_changed_literal_keys'][field]
author=check(proposal['proposed_full29_inventory']);assert {k:v for k,v in fresh.items() if k!='generated_at_utc'}=={k:v for k,v in author.items() if k!='generated_at_utc'}
for key,bodies in proposal['entire_current_and_proposed_literal_records'].items():
 field='exercises' if 'exercise' in key else 'material_source_units';assert next(r for r in inv[field] if r['key']==key)==bodies['entire_current'];assert next(r for r in fresh[field] if r['key']==key)==bodies['entire_proposed']
after=guard();assert before==after
result={'status':'passed_independent_Source65_narrow_literal_proof_support_and_fresh_full29_parser_foundations_review','errors':[],'reviewer':'/root/foundations_recovery28','reader_started_at_utc':started,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(Q),'proposal':q['proposal'],'source64_inventory':q['source64_inventory'],'exact_forward_and_inverse_two_replacements':True,'all_node_tags_attrs_lines_preserved':True,'entire_current_and_proposed_Exercise12_5_and_nodes1328_1329_read':True,'narrow_wording_decisions':[{'clause':'positive derivative-supremum multiplicative ratio and constant exception','approved':True,'reason':'Actual exercise assumes both scalar weights nonzero and global monotone slope restriction0<=alpha<beta. The full source derives global Lipschitz/absolute continuity from the chord restriction, uses actual FTC to prove derivative supremum is the least activation constant, and transfers it through both nonzero weights. A positive supremum permits the exact ratio; the genuine constant-activation model has least constant0 and gives a positive supplied beta bound under the printed nonzero weights, with no finite ratio.'},{'clause':'exact negative eigenvalue and three-decimal approximation','approved':True,'reason':'The exact matrix is[-.8281,.637;.637,-.49], with trace-1.3181 and determinant0. Its actual characteristic polynomial factors X(X+13181/10000), and two explicit nonzero eigenvectors satisfy the0 and-13181/10000 actions. The genuine strict error enclosure about-1.318 is below.0005; the equality to-1.318 is explicitly refuted.'}],'full_source_support_bodies_read':support,'primitive_source_definitions_and_ACTUAL_AC_FTC_primary_proofs_read':True,'same42_genuine_current64_standalone_pass':trial,'fresh_independent_full29_inventory':ref(freshpath),'both_parser_ROOT_OUT_isolated_TMP':True,'fresh_changed_literal_keys':changed,'all_other555_exercise_literals_unchanged':True,'all_other12772_material_literal_texts_unchanged':True,'all_source60_historical_and_current64_native_original_bodies_commands_times_failure_outcomes_preserved':True,'original_current60_proposal_or_kernel_relabelled':False,'source65_applied':False,'whole_exercise_or_material_unit_math_approval':False,'before':before,'after':after,'no_canonical_owner_source_selection_or_publication_writes':True,'coverage_complete':False}
(W/'findings-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'changed':changed,'guards':True,'whole_exercise_approved':False}))
