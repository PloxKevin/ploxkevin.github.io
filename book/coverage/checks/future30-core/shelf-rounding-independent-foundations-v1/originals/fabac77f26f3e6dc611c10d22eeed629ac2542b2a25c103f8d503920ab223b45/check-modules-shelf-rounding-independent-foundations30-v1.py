from pathlib import Path
from datetime import datetime, timezone
import contextlib, hashlib, importlib.util, json, re, sys, tempfile
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=Path('/tmp/modules-shelf-rounded-coefficients-unnumbered-proposal30-v1/modules-shelf-rounded-coefficients-unnumbered-full29-proposal30-v1.json')
OUT=Path('/tmp/modules-shelf-rounding-independent-foundations30-findings-v1.json')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(q):
    p=Path(q['file']);return p if p.is_absolute() else ROOT/p
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
assert sha(REQUEST)=='9159be0b8b5d00de112fea75b279e6bbfed224731bc9f9301d0844c529a8f7bd'
d=json.loads(REQUEST.read_bytes())
assert d['prospective_source_number'] is None and d['source_number_reserved'] is False and d['source_applied'] is False
assert d['both_parser_ROOT_and_OUT_isolated'] is True and len(d['exact_replacements'])==8
for k in ['source','before_inventory','before_corrections','parser','validator','proposed_source','original_owner29_candidate','proposed_full29_inventory','actual_parser_stdout','actual_supporting_full_shelf_threshold_and_coefficient_ratio_rounding_source','actual_supporting_passed_trial5','actual_supporting_source_snapshot','actual_supporting_raw_log']:
    assert sha(path(d[k]))==d[k]['sha256'],k
raw=path(d['source']).read_text();proposed=path(d['proposed_source']).read_text()
forward=raw
for row in d['exact_replacements']:
    assert forward.count(row['before'])==1 and row['after'] not in forward
    forward=forward.replace(row['before'],row['after'],1)
assert forward==proposed
inverse=proposed
for row in reversed(d['exact_replacements']):
    assert inverse.count(row['after'])==1
    inverse=inverse.replace(row['after'],row['before'],1)
assert inverse.encode()==path(d['source']).read_bytes()
assert d['full_current_shelf_exercise_context_lines907_921']==''.join(raw.splitlines(keepends=True)[906:921])
assert d['full_proposed_shelf_exercise_context_lines907_921']==''.join(proposed.splitlines(keepends=True)[906:921])
sys.path.insert(0,str(ROOT/'book'))
from validate import Document
assert [(n.tag,n.attrs,n.line) for n in Document(raw).nodes]==[(n.tag,n.attrs,n.line) for n in Document(proposed).nodes]
iso=Path(tempfile.mkdtemp(prefix='shelf-rounding-independent-full29-parser30-',dir='/tmp'))
(iso/'SafeLearning').mkdir()
for src in (ROOT/'SafeLearning').glob('*.html'):
    (iso/'SafeLearning'/src.name).write_bytes(proposed.encode() if src.name=='viability.html' else src.read_bytes())
assert len(list((iso/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('shelf_rounding_independent_isolated_inventory30',ROOT/'book/inventory_claims.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.ROOT=iso;m.OUT=iso/'book/coverage'
assert m.ROOT.resolve().is_relative_to(Path('/tmp')) and m.OUT.resolve().is_relative_to(iso)
parserlog=iso/'independent-full29-parser.log'
with parserlog.open('x') as f,contextlib.redirect_stdout(f):m.inventory()
freshpath=m.OUT/'inventory.json';fresh=json.loads(freshpath.read_bytes());old=json.loads(path(d['before_inventory']).read_bytes())
assert fresh['counts']==old['counts']==d['parser_counts']
assert {n for n in old['source_sha256'] if old['source_sha256'][n]!=fresh['source_sha256'][n]}=={'SafeLearning/viability.html'}
assert set(fresh['source_sha256'])==set(old['source_sha256'])
changed={}
for family in ['exercises','material_source_units']:
    a={r['key']:r for r in old[family]};b={r['key']:r for r in fresh[family]}
    assert a.keys()==b.keys();changed[family]=[]
    for key,row in a.items():
        if row['source_text']!=b[key]['source_text']:changed[family].append(key)
        if row['source']!='SafeLearning/viability.html':assert row==b[key],key
        else:
            assert {k:v for k,v in row.items() if k not in ['source_text','text_sha256','source_sha256']}=={k:v for k,v in b[key].items() if k not in ['source_text','text_sha256','source_sha256']},key
            assert b[key]['source_sha256']==d['proposed_source']['sha256']
            assert hashlib.sha256(b[key]['source_text'].encode()).hexdigest()==b[key]['text_sha256']
assert changed==d['fresh_changed_literal_keys']=={'exercises':['viability.html::exercise-17'],'material_source_units':['viability.html::node-1126']}
for key,rows in d['entire_current_and_proposed_literal_records'].items():
    family='exercises' if '::exercise-' in key else 'material_source_units'
    assert rows['entire_current']==next(r for r in old[family] if r['key']==key)
    assert rows['entire_proposed']==next(r for r in fresh[family] if r['key']==key)
author=json.loads(path(d['proposed_full29_inventory']).read_bytes())
assert {k:v for k,v in author.items() if k!='generated_at_utc'}=={k:v for k,v in fresh.items() if k!='generated_at_utc'}
native=json.loads(path(d['actual_supporting_passed_trial5']).read_bytes())
for k in ['exit_code','actual_exit_code','actual_runner_exit_code']:
    if k in native:assert type(native[k]) is int and native[k]==0
assert native['actual_command']==['lake','env','lean',native['source']]
assert native['actual_workdir']==str(ROOT/'verification/lean')
assert native['status']=='passed_actual_tmp_lean_only' and native['protection_errors']==[] and native['source_unchanged'] is True
assert native['source_sha256_before']==native['source_sha256_after']==native['source_snapshot_sha256']==d['actual_supporting_full_shelf_threshold_and_coefficient_ratio_rounding_source']['sha256']==d['actual_supporting_source_snapshot']['sha256']
assert native['raw_log_sha256']==d['actual_supporting_raw_log']['sha256']
assert [native[k] for k in ['protected_selected29_proof_sources','unchanged_current65_book_assets','unchanged_installed29_live_owners']]==[1197,31,5]
support=path(d['actual_supporting_full_shelf_threshold_and_coefficient_ratio_rounding_source']).read_text()
required_names=['actual_extra_failure_time_scales_the_shifted_threshold','actual_exp_quadratic_remainder_bound','actual_exponential_natural_multiple_enclosure','actual_shelf_tau1_failure1_two_decimal_rounding','actual_shelf_tau1_failure2_two_decimal_rounding','actual_shelf_tau_half_two_decimal_rounding','actual_shelf_tau_two_two_decimal_rounding','actual_shelf_tau_five_two_decimal_rounding','actual_shelf_tau_twenty_two_decimal_rounding','actual_shelf_p_itself_delay_ratio_rounds_to_three_point_one','actual_shelf_exp_neg_five_four_decimal_rounding','actual_shelf_exp_neg_two_point_five_three_decimal_rounding','actual_shelf_exp_neg_one_three_decimal_rounding','actual_shelf_exp_neg_quarter_three_decimal_rounding']
assert all('theorem '+n in support for n in required_names)
owner=json.loads((ROOT/'book/coverage/modules.json').read_bytes())
assert d['exact_current_owned_exercise_body']==next(r for r in owner['exercises'] if r['inventory_key']=='viability.html::exercise-17')
assert d['exact_current_owned_changed_material_claim_rows']==[r for r in owner['material_claims'] if 'viability.html::node-1126' in r.get('source_unit_keys',[])]
assert all(d[k] is False for k in ['compiler_canonical_owner_selection_or_publication_mutations','coverage_complete'])
result={'status':'passed_independent_narrow_shelf_rounding_full_literals_and_fresh_isolated29_parser_review','errors':[],
    'request':ref(REQUEST),'finished_at_utc':datetime.now(timezone.utc).isoformat(),
    'fresh_full29_inventory':ref(freshpath),'fresh_full29_parser_log':ref(parserlog),
    'both_ROOT_and_OUT_strictly_TMP':True,'exact_forward_and_inverse':True,'all_nodes_tags_attrs_lines_equal':True,
    'changed_literal_keys':changed,'counts':fresh['counts'],'all_other555_exercise_texts_and_other_material_literals_and28_pages_exact':True,
    'supporting_pass_original_retained_without_recompilation':True,
    'supporting_actual_emitted_warning_count':len(re.findall(r'^.*:\d+:\d+: warning:',path(d['actual_supporting_raw_log']).read_text(),re.M)),
    'full_current_proposed_exercise17_node1126_and_context_read':True,'full_support29_and_used_exp_Taylor_power_scaling_proofs_read':True,
    'narrow_wording_approved':True,
    'mathematical_reason':'The exact shelf threshold is tau*(2-exp(-5/tau))*exp(Tf/tau)-tau. Replacing its exponential coefficients by rounded .0067,1.918,1.632 or1.221 permits approximation, not equality. Exactly five such equality signs become approximation symbols. The exact decimal subtractions5.418-1=4.418 and7.389-.5=6.889 differ from their two-decimal displayed targets, so those two equality signs also become approximation symbols. Other displayed decimal subtractions are genuine equalities and remain unchanged. The actual shifted threshold p+tau scales exactly by exp(delay/tau); p itself need not have that ratio. The proved ratio lies strictly between3.05 and3.15, justifying approximately3.1. The supporting kernel proofs derive coefficient nearest-rounding intervals and all six original two-decimal targets from genuine Taylor bounds and exponential power identities, with no desired exponential or threshold bounds as premises. All exact parameter hypotheses, mathematical formulas and every other exercise/material literal remain unchanged. Global shape/minimum and the cited primary figure are outside this eight-phrase narrow approval and remain with the separate full exercise reviewer.',
    'actual_supporting_passed_trial5':d['actual_supporting_passed_trial5'],'actual_supporting_source':d['actual_supporting_full_shelf_threshold_and_coefficient_ratio_rounding_source'],
    'source_ordinal_reserved':False,'source_applied':False,'whole_exercise_or_whole_node1126_or_whole57_approval_inferred':False,
    'coverage_complete':False}
OUT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'findings':ref(OUT),'changed':changed,'supporting_warnings':result['supporting_actual_emitted_warning_count'],'parser_ROOT_OUT_TMP':True}))
