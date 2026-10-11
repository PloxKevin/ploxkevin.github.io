from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,importlib.util,sys,shutil,re
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
sha=H
read=lambda p:json.loads(Path(p).read_text())
def path(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def ref(p):return {'file':str(p),'sha256':H(p)}
def bind(r):
 p=path(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];return p
REQUEST=TMP/'modules-nn-tanh-precision-temporal-scope-proposal52-v1.json'
OUT=TMP/'modules-nn-tanh52-proposal-independent-foundations-semantic-and-parser-review-v3.json'
assert not OUT.exists()and H(REQUEST)=='ed3048a29f91b4f68201af308429831bc094e560db99f48a8b6ffb19851ff9fe'
q=read(REQUEST)
def simulate(q,baseline_inventory,baseline_tree,label):
 source=q['source'];original=(baseline_tree/source).read_bytes();assert hashlib.sha256(original).hexdigest()==q['source_sha256_before']
 after=original
 for row in q['replacements']:
  a,b=row['before'].encode(),row['after'].encode()
  assert after.count(a)==1 and b'\n' not in a and b'\n' not in b and row['count']==1
  after=after.replace(a,b,1)
 reverse=after
 for row in reversed(q['replacements']):
  a,b=row['before'].encode(),row['after'].encode();assert reverse.count(b)==1;reverse=reverse.replace(b,a,1)
 assert reverse==original and after.count(b'\n')==original.count(b'\n')
 assert hashlib.sha256(after).hexdigest()==q['proposed_source_sha256_after']
 from validate import Document
 old_doc,new_doc=Document(original.decode()),Document(after.decode())
 assert len(old_doc.nodes)==len(new_doc.nodes)
 assert [(n.tag,n.attrs,n.line) for n in old_doc.nodes]==[(n.tag,n.attrs,n.line) for n in new_doc.nodes]
 sim=TMP/f'foundations-independent-tanh52-proposal24-{label}-simulation-v3'
 assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
 for p in (baseline_tree/'SafeLearning').glob('*.html'):
  shutil.copyfile(p,sim/'SafeLearning'/p.name)
 (sim/source).write_bytes(after)
 spec=importlib.util.spec_from_file_location('foundation_precision_inventory_'+label,ROOT/'book/inventory_claims.py')
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 module.ROOT=sim;module.OUT=sim/'book/coverage';module.inventory()
 parsed=read(module.OUT/'inventory.json');assert parsed['counts']==baseline_inventory['counts']
 assert len(parsed['source_sha256'])==len(baseline_inventory['source_sha256'])==29
 assert set(parsed['source_sha256'])==set(baseline_inventory['source_sha256'])
 assert {n for n in parsed['source_sha256'] if parsed['source_sha256'][n]!=baseline_inventory['source_sha256'][n]}=={source}
 changes={}
 for section in ('exercises','material_source_units'):
  old={r['key']:r for r in baseline_inventory[section]};new={r['key']:r for r in parsed[section]}
  assert old.keys()==new.keys();changed=[]
  for key,a in old.items():
   b=new[key];assert a.keys()==b.keys()
   assert all(a[f]==b[f] for f in a if f not in {'source_sha256','source_text','text_sha256'}),(label,key)
   if a['source_text']!=b['source_text']:changed.append(key)
   else:assert a['text_sha256']==b['text_sha256']
   if a['source']!=source:assert a==b
  changes[section]=changed
 assert changes==q['expected_changed_text_keys']
 return {'baseline':label,'actual_fresh_full29_page_parser_completed':True,'simulation_inventory':ref(module.OUT/'inventory.json'),'only_changed_literal_keys':changes,'all_keys_lines_attributes_locators_and_other_fields_exact':True,'DOM_signature_exact':True,'unique_forward_reverse_and_newline_bytes_exact':True}


invp=ROOT/q['inventory'];inv=read(invp)
assert H(invp)==H(ROOT/'book/coverage/inventory.json')==q['inventory_sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
page=ROOT/q['source'];assert H(page)==q['source_sha256_before']=='413846b5ffc2a5fd70f74fb6f4a24e96b7983b6a745f50340c9d2d25c75d7049'
assert bind(q['source_bytes_before_snapshot']).read_bytes()==page.read_bytes()
afterp=bind(q['source_bytes_proposed_after_snapshot']);after=afterp.read_bytes()
assert q['proposed_source_sha256_after']==H(afterp)=='1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'
assert len(q['replacements'])==2
for row in q['replacements']:assert row['count']==1
assert '<strong>(b)</strong>'in q['replacements'][0]['before']and '<strong>(c)</strong> Bias-free'in q['replacements'][1]['before']

assert q['expected_changed_text_keys']=={'exercises':['nn-in-the-loop.html::exercise-20'],'material_source_units':['nn-in-the-loop.html::node-1260','nn-in-the-loop.html::node-1262']}
oldpeer=read(bind(q['original_semantic_component_peers'][0]));newpeer=read(bind(q['original_semantic_component_peers'][1]))
assert oldpeer['errors']==newpeer['errors']==[]and'passed'in oldpeer['status']and'passed'in newpeer['status']
assert newpeer['entire_original_nine_body_semantics_and_time_unchanged']==oldpeer
sources=[]
for rr in q['actual_proof_sources']:
 p=bind(rr);sources.append({'reference':rr,'entire_original_source_and_bodies':p.read_text()});assert not re.search(r'\b(sorry|admit|axiom)\b',p.read_text())
assert oldpeer['entire_new_source_and_all_nine_bodies']==sources[0]['entire_original_source_and_bodies']
assert newpeer['new_sources'][0]['entire_source_and_all_twelve_bodies']==sources[1]['entire_original_source_and_bodies']
assert newpeer['new_sources'][1]['entire_source_and_all_four_bodies']==sources[2]['entire_original_source_and_bodies']
for row in q['actual_original_TMP_zero_records']:
 p=bind(row['record']);r=read(p);assert r==row['entire_original_record_body_and_time']and r['actual_exit_code']==0
 assert r['actual_workdir']==str(ROOT/'verification/lean')and r['actual_command']==['lake','env','lean',r['source']]
 assert H(Path(r['source']))==r['source_sha256_before']==r['source_sha256_after']
 assert H(Path(r['raw_log']))==r['raw_log_sha256']and Path(r['raw_log']).read_bytes()==b''
 assert H(Path(r['actual_runner']))==r['actual_runner_sha256']
context=q['direct_local_Section3_source_context'];assert context['source_sha256']==H(page)
context_lines=page.read_text().splitlines(keepends=True)[context['lines_start']-1:context['lines_end']]
assert context_lines[-1]=='\n' and ''.join(context_lines[:-1])==context['exact_lines']
context_boundary={'entire_declared_line_range':''.join(context_lines),'author_exact_excerpt':context['exact_lines'],'only_omitted_last_blank_line':'\n','all_mathematical_context_bytes_exact':True}
first_reader=read(TMP/'modules-tanh52-proposal-independent-foundations-actual-v1.json')
assert first_reader['actual_exit_code']==1 and H(TMP/'modules-tanh52-proposal-independent-foundations-check-v1.py')==first_reader['actual_checker_sha256_before']==first_reader['actual_checker_sha256_after']
assert H(Path(first_reader['raw_log']))==first_reader['raw_log_sha256']
second_reader=read(TMP/'modules-tanh52-proposal-independent-foundations-actual-v2.json')
assert second_reader['actual_exit_code']==1 and H(TMP/'modules-tanh52-proposal-independent-foundations-check-v2.py')==second_reader['actual_checker_sha256_before']==second_reader['actual_checker_sha256_after']
assert H(Path(second_reader['log']))==second_reader['log_sha256']
primary=ROOT/'sources/text/2103.17106.txt';primarytext=primary.read_text()
assert 'arXiv:2103.17106v2' in primarytext and '30 Sep 2021'in primarytext
passages=[{'source':ref(primary),'lines_start':a,'lines_end':b,'exact_lines':''.join(primarytext.splitlines(keepends=True)[a-1:b])}for a,b in[(105,141),(249,352),(354,396),(570,673)]]
assert 'not identical'in passages[0]['exact_lines']
assert 'If φ̃ is not diagonally repeated'in passages[1]['exact_lines']and 'zero for k < 0'in passages[1]['exact_lines']
assert 'Non-repeated nonlinearities'in passages[3]['exact_lines']and'doubly hyperdominant'in passages[3]['exact_lines']
before_ex=next(e for e in inv['exercises']if e['key']=='nn-in-the-loop.html::exercise-20')
before_units=[u for u in inv['material_source_units']if u['key']in q['expected_changed_text_keys']['material_source_units']]
assert before_ex==oldpeer['exercise']['entire_inventory_record']and len(before_units)==2
helper=bind(q['proposal_helper']);actualp=TMP/'modules-tanh52-precision-scope-proposal-actual-v2.json';actual=read(actualp)
assert actual['actual_exit_code']==0 and actual['actual_command']==['python3',str(helper)]and actual['actual_workdir']==str(ROOT)
assert actual['actual_checker_sha256_before']==actual['actual_checker_sha256_after']==H(helper)
assert H(Path(actual['log']))==actual['log_sha256']and actual['started_at_utc']<actual['finished_at_utc']
failure=q['preserved_first_proposal_reader_failure'];fp=bind(failure['actual_execution']);failed=read(fp)
assert failed['actual_exit_code']==1 and H(bind(failure['raw_log']))==failed['log_sha256']
assert H(bind(failure['checker']))==failed['actual_checker_sha256_before']==failed['actual_checker_sha256_after']
sys.path.insert(0,str(ROOT/'book'));simulation=simulate(q,inv,ROOT,'source51')
fresh=read(Path(simulation['simulation_inventory']['file']));author=read(bind(q['fresh_full29_parser']['simulated_inventory']))
assert fresh['counts']==author['counts']==inv['counts']
assert fresh['exercises']==author['exercises']and fresh['material_source_units']==author['material_source_units']and fresh['source_sha256']==author['source_sha256']
assert simulation['only_changed_literal_keys']==q['expected_changed_text_keys']
selectionp=ROOT/'reports/full-coverage/checkpoint-23-selection.json';selection=read(selectionp);manifest=read(ROOT/'reports/full-coverage/checkpoint-23-manifest.json')
assert len(selection['proof_files'])==1131
for n,r in selection['proof_files'].items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==r['sha256']
assets={n:h for n,h in manifest['working_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
for n,h in assets.items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==h
for n,h in q['live_owner_and_inventory_bytes_at_preparation'].items():assert H(ROOT/n)==h,n
assert H(ROOT/'book/coverage/inventory.json')==q['inventory_sha256']and H(page)==q['source_sha256_before']
proposed_units=[u for u in fresh['material_source_units']if u['key']in q['expected_changed_text_keys']['material_source_units']]
assert len(proposed_units)==2
semantic=[{'clause':'six_decimal_approximation_and_strict_actual_sign','approved':True,'reason':'All four coupled displays and both diagonal products are now marked approximate or verbal approximations. Original exact transcendental source and rational bounds prove each nearest displayed precision and strict non-equality; the actual QC difference expression is exactly the source difference product, and its negativity is genuinely proved, not rounded-sign inference. Both true diagonal products are nonnegative.'},
 {'clause':'invalid_QC_premise_scope','approved':True,'reason':'The true negative witness contradicts a QC asserted for all shifted inputs. The correction accurately states an invalid generally-valid premise, and explicitly avoids claiming this witness alone makes every particular final stability conclusion false.'},
 {'clause':'independent_static_circle_and_full_block_scope','approved':True,'reason':'Each translated channel vanishes at0 and keeps its genuine[0,1] chord slopes. The selected component peers include internal independent gain witnesses plus actual robust all-D matrix PSD⇒all-input quadratic nonnegativity. Primary SectionII-C equations5–6 independently confirm every diagonal-sector graph admits the full-block static constraint; no repeated functions are assumed. Equal centers and arbitrary-depth bias-free origin remain correct.'},
 {'clause':'ordinary_diagonal_temporal_ZF_scope_from_primary','approved':True,'reason':'Primary SectionII-D states the sign and row/column sum restrictions, actual slope transformation and hard-IQC theorem for square-summable graph signals zero-padded before0; its non-repeated specialization explicitly takes diagonal Mj. AppendixB proves finite-horizon nonnegativity and repeats that specialization. The corrected paragraph explicitly depends on all Section3 assumptions, not time invariance alone. Zero-centered shifted channels provide legitimate zero padding; each channel has its own bounds. This is an accurate primary-theorem attribution, without claiming a new Lean arbitrary-horizon proof.'},
 {'clause':'odd_class_extra_actual_shifted_oddness','approved':True,'reason':'Primary SectionII-D enlarges permissible signs only under actual oddness. The proposal retains that additional property of the shifted channel. A nonzero tanh center generally destroys oddness; in the exact center2 example, g(2)+g(-2)=tanh4−2tanh2<0 using tanh4<1 and the already proved tanh2>0.964, so the shift is concretely not odd. Bias-free origin tanh remains odd. No unproved claim that every other shifted activation is nonodd is made.'}]
report={'status':'passed_independent_source52_two_paragraph_semantics_primary_scope_exact_bytes_and_fresh_full29_parser_proposal_only','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'checker':ref(Path(__file__)),'original_proposal':ref(REQUEST),'entire_original_proposal_body_and_time':q,'semantic_decisions':semantic,'proposal_text_approved':True,'whole_exercise_or_material_unit_approved':False,'original_full_source51_exercise':before_ex,'original_two_material_records':before_units,'proposed_two_material_records':proposed_units,'original_precision_and_static_component_peers':[{'reference':q['original_semantic_component_peers'][0],'entire_original_peer_body_and_time':oldpeer},{'reference':q['original_semantic_component_peers'][1],'entire_original_peer_body_and_time':newpeer}],
 'full_original_actual_proof_sources_and_bodies':sources,'primary_arxiv_v2_passages_read':passages,'direct_exact_local_Section3_context':context,'explicit_excerpt_blank_line_boundary':context_boundary,'preserved_second_independent_reader_schema_failure':{'reader':ref(TMP/'modules-tanh52-proposal-independent-foundations-check-v2.py'),'actual':ref(TMP/'modules-tanh52-proposal-independent-foundations-actual-v2.json'),'raw_log':ref(TMP/'modules-tanh52-proposal-independent-foundations-actual-v2.log'),'entire_original_actual_body_and_time':read(TMP/'modules-tanh52-proposal-independent-foundations-actual-v2.json'),'cause':'Reader-v2 used log instead of the original actual-v1 raw_log key; new reader-v3 honors the exact original schema.'},'preserved_first_independent_reader_failure':{'reader':ref(TMP/'modules-tanh52-proposal-independent-foundations-check-v1.py'),'actual':ref(TMP/'modules-tanh52-proposal-independent-foundations-actual-v1.json'),'raw_log':ref(Path(first_reader['raw_log'])),'entire_original_actual_body_and_time':first_reader,'cause':'Author excerpt binds all mathematical text at271–306 but omits the final blank line307 inside the inclusive declared range; reader-v2 verifies that exact one blank newline explicitly, without changing author source/request or semantic text.'},'actual_original_preparer_record_and_time':actual,'actual_original_preparer_rawlog':ref(Path(actual['log'])),'actual_first_preparer_failure_retained':{'entire_original_record_and_time':failed,'original_references':failure},'independent_fresh_full29_page_parser':simulation,'all_other_28_pages_DOM_keys_lines_attributes_and_literals_exact':True,'only_changed_literal_keys':q['expected_changed_text_keys'],'all1131_frozen23_sources_and31_assets_exact':True,'all_live_owner_inventory_guards_exact':q['live_owner_and_inventory_bytes_at_preparation'],'errors':[],'coverage_complete':False,'remaining_whole_semantic_and_formal_gaps':q['remaining_semantic_gaps_preserved'],'scope':'TMP-only new semantic/primary/proposal correspondence and genuine fresh parser execution. Source51 HTML/inventory/current23 owners and proof selection unchanged; no assignment/application of52, whole Exercise14.6/answers promotion, new temporal Lean proof, canonical compiler or Pages claim. Original component bodies/times and every failed/pass trial retained exact.'}
with OUT.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'report':ref(OUT),'proposal_approved':True,'fresh29_parser':True,'only_changed_keys':q['expected_changed_text_keys']}))
