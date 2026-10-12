from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, sys, tempfile
sys.dont_write_bytecode=True

ROOT = Path('/home/oxrexkevin/SafetyBased')
REQUEST = Path('/tmp/modules-duality-oscillation-unnumbered-proposal30-v1/modules-duality-oscillation-unnumbered-full29-proposal30-v1.json')
CONTEXT = Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
OUT = Path('/tmp/modules-duality-oscillation-independent-foundations30-findings-v1.json')
assert not OUT.exists()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(q):
    p = Path(q['file'])
    return p if p.is_absolute() else ROOT/p
def ref(p):
    p = Path(p)
    return {'file': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
assert sha(REQUEST) == 'a222074bcf42de1f7f5273d58d47dd2c58d54c84aa8bdb71356dce32c41479c9'
assert sha(CONTEXT) == 'ed8ca5f56d1f101b1a5898e367162bda47bd6b0845312ce3ba2dda4d58938ae2'
d = json.loads(REQUEST.read_bytes())
assert d['prospective_source_number'] is None and d['source_number_reserved'] is False
assert d['source_applied'] is False and d['both_parser_ROOT_and_OUT_isolated'] is True
for k in ['source', 'before_inventory', 'before_corrections', 'parser', 'validator', 'proposed_source']:
    assert sha(path(d[k])) == d[k]['sha256']
raw, proposed = path(d['source']).read_text(), path(d['proposed_source']).read_text()
forward = raw
for row in d['exact_replacements']:
    assert forward.count(row['before']) == 1
    forward = forward.replace(row['before'], row['after'])
assert forward == proposed
inverse = proposed
for row in reversed(d['exact_replacements']):
    assert inverse.count(row['after']) == 1
    inverse = inverse.replace(row['after'], row['before'])
assert inverse == raw
sys.path.insert(0, str(ROOT/'book'))
from validate import Document
assert [(n.tag, n.attrs, n.line) for n in Document(raw).nodes] == [(n.tag, n.attrs, n.line) for n in Document(proposed).nodes]
iso = Path(tempfile.mkdtemp(prefix='duality-oscillation-independent-full29-parser30-', dir='/tmp'))
(iso/'SafeLearning').mkdir()
for src in (ROOT/'SafeLearning').glob('*.html'):
    (iso/'SafeLearning'/src.name).write_bytes(proposed.encode() if src.name == 'viability.html' else src.read_bytes())
assert len(list((iso/'SafeLearning').glob('*.html'))) == 29
spec = importlib.util.spec_from_file_location('duality_oscillation_independent_isolated_inventory30', ROOT/'book/inventory_claims.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
m.ROOT = iso
m.OUT = iso/'book/coverage'
assert m.ROOT.resolve().is_relative_to(Path('/tmp')) and m.OUT.resolve().is_relative_to(iso)
m.inventory()
fresh_path = m.OUT/'inventory.json'
fresh = json.loads(fresh_path.read_bytes())
old = json.loads(path(d['before_inventory']).read_bytes())
assert fresh['counts'] == old['counts']
assert set(fresh['source_sha256']) == set(old['source_sha256'])
assert {n for n in old['source_sha256'] if old['source_sha256'][n] != fresh['source_sha256'][n]} == {'SafeLearning/viability.html'}
changed = {}
for family in ['exercises', 'material_source_units']:
    a = {r['key']: r for r in old[family]}
    b = {r['key']: r for r in fresh[family]}
    assert set(a) == set(b)
    changed[family] = []
    for key, row in a.items():
        if row['source_text'] != b[key]['source_text']:
            changed[family].append(key)
        for field, value in row.items():
            if field not in ['source_text', 'text_sha256', 'source_sha256']:
                assert b[key][field] == value, (key, field)
        if row['source'] != 'SafeLearning/viability.html':
            assert row == b[key], key
assert changed == d['fresh_changed_literal_keys']
for key, rows in d['entire_current_and_proposed_literal_records'].items():
    family='exercises' if '::exercise-' in key else 'material_source_units'
    assert rows['entire_current'] == next(r for r in old[family] if r['key'] == key)
    assert rows['entire_proposed'] == next(r for r in fresh[family] if r['key'] == key)
assert d['full_current_duality_exercise_context_lines941_957'] == ''.join(raw.splitlines(keepends=True)[940:957])
assert d['full_proposed_duality_exercise_context_lines941_957'] == ''.join(proposed.splitlines(keepends=True)[940:957])
for k in ['actual_supporting_positive_budget_no_oscillation_countermodel_source','actual_supporting_passed_trial10','actual_supporting_source_snapshot','actual_supporting_raw_log']:
    assert sha(path(d[k]))==d[k]['sha256']
native=json.loads(path(d['actual_supporting_passed_trial10']).read_bytes())
assert type(native['actual_exit_code'])is int and native['actual_exit_code']==0 and native['protection_errors']==[]
assert native['actual_command']==['lake','env','lean',native['source']] and native['actual_workdir']==str(ROOT/'verification/lean')
assert d['actual_supporting_positive_budget_no_oscillation_countermodel_source']['sha256']==native['source_sha256_before']==native['source_sha256_after']==native['source_snapshot_sha256']
assert native['raw_log_sha256']==d['actual_supporting_raw_log']['sha256'] and native['source_unchanged']is True and type(native['actual_runner_exit_code'])is int and native['actual_runner_exit_code']==0
assert [native[k]for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
support=path(d['actual_supporting_positive_budget_no_oscillation_countermodel_source']).read_text()
assert 'actual_positive_budget_zero_cost_exact_maximizer_process_does_not_oscillate' in support
owner=json.loads((ROOT/'book/coverage/modules.json').read_bytes())
assert d['exact_current_owned_exercise_body']==next(r for r in owner['exercises']if r['inventory_key']=='viability.html::exercise-19')
assert d['exact_current_owned_changed_material_claim_rows']==[r for r in owner['material_claims']if 'viability.html::node-1162'in r.get('source_unit_keys',[])]
assert all(d[k]is False for k in ['compiler_canonical_owner_selection_or_publication_mutations','coverage_complete'])
assert d['exact_replacements']==[{'before':'the multiplier and the cost oscillate around the constraint boundary','after':'the multiplier and the cost can oscillate around the constraint boundary'}]
assert changed=={'exercises':['viability.html::exercise-19'],'material_source_units':['viability.html::node-1162']}
pid=ROOT/'sources/text/pid_raw.txt'; pid_text=pid.read_text()
assert 'arXiv:2007.03964v1' in pid_text and 'cost and multiplier values oscillated throughout training' in pid_text
result={
 'status':'passed_independent_full_narrow_duality_can_oscillate_literal_and_fresh_isolated29_parser_review',
 'request':ref(REQUEST),'context':ref(CONTEXT),'finished_at_utc':datetime.now(timezone.utc).isoformat(),
 'fresh_full29_inventory':ref(fresh_path),'both_ROOT_and_OUT_strictly_TMP':True,'exact_forward_and_inverse':True,
 'all_nodes_tags_attrs_lines_equal':True,'only_one_expected_exercise_answer_text_changes_all_other555_exact':True,
 'all_other_material_literal_texts_unchanged':True,'changed_literal_keys':changed,'counts':fresh['counts'],
 'source_ordinal_reserved':False,'source_applied':False,'whole_units_promoted':[],
 'narrow_wording_approved':True,'exact_single_phrase_replacement_approved':True,
 'entire_current_proposed_exercise7_5_node1162_and_local_context_read':True,
 'actual_supporting_constant_zero_cost_countermodel_body_and_definitions_read':True,
 'supporting_original_genuine31_pass_retained_without_recompilation':True,
 'original_Dual55_and_Dual68_full_scope_approvals_retained_separately':True,
 'primary_PID_paper_text':ref(pid),'primary_PID_url':'https://arxiv.org/abs/2007.03964',
 'full_used_primary_introduction_Figure1_and_section6_3_context_read':True,
 'mathematical_reason':'The current unqualified sentence is a universal prediction from positive budget and approximate sampled maximizers. A genuine one-action flat zero-reward/zero-cost problem has actual global maximizers at every penalty; for positive eta and budget, max(0,0+eta(0-budget))=0 and the actual constant-zero multiplier process has zero increments. Deterministic zero-cost samples are exact at every sample; exact maximizers meet any positive inexact tolerance. Thus oscillation is not universal. The primary PID paper introduction and Figure1 explicitly report oscillating episodic costs and multipliers on DoggoButton1, and Section6.3 reports this behavior changing with integral gains. Replacing only oscillate by can oscillate faithfully states that documented possibility while keeping the motivation for the PID multiplier. It neither asserts all deep-RL algorithms oscillate nor promises PID convergence. The zero-budget exact-maximizer clauses, general LP/DP claims, actual Chain association and other parts of the exercise are unchanged and retain their separate review statuses.',
 'whole_exercise7_5_or_whole_node1162_approved':False,
 'compiler_parser_live_source_owner_canonical_publication_mutation':False,
 'coverage_complete':False,'errors':[]}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'changed':changed,'parser_ROOT_OUT_TMP':True}))
