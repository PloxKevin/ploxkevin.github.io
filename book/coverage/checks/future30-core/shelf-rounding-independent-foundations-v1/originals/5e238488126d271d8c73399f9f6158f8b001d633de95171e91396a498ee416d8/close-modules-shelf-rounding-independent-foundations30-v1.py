from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/future30-core/shelf-rounding-independent-foundations-v1'
assert not BASE.exists()
FIND=Path('/tmp/modules-shelf-rounding-independent-foundations30-findings-v1.json')
ACTUAL=Path('/tmp/modules-shelf-rounding-independent-foundations30-actual-v1.json')
CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(q):
    p=Path(q['file']);return p if p.is_absolute() else ROOT/p
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':sha(p),'bytes':p.stat().st_size}
ctx=json.loads(CONTEXT.read_bytes());protected={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']}
assert all(sha(ROOT/n)==h for n,h in protected.items())
d=json.loads(FIND.read_bytes());a=json.loads(ACTUAL.read_bytes())
assert a['status']=='passed' and type(a['actual_exit_code']) is int and a['actual_exit_code']==0 and a['protection_errors']==[]
assert a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['log'])==a['log_sha256']
assert d['errors']==[] and d['narrow_wording_approved'] is True
REQUEST=Path(d['request']['file']);proposal=json.loads(REQUEST.read_bytes())
aliases={};closed={}
def bind(p):
    p=Path(p);p=p if p.is_absolute() else ROOT/p;h=sha(p)
    if p.is_relative_to(ROOT) and p.resolve().is_relative_to(ROOT) and (p.name=='inventory-after-correction65.json' or 'current65-pair-bound-v7' in str(p)):
        q=p
    else:
        q=BASE/'originals'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
        if q.exists():assert sha(q)==h
        else:
            with q.open('xb') as f:f.write(p.read_bytes())
    aliases[str(p)]=ref(q);closed[str(q.relative_to(ROOT))]=h;return ref(q)
for k in ['source','before_inventory','before_corrections','parser','validator','proposed_source','original_owner29_candidate','proposed_full29_inventory','actual_parser_stdout','actual_supporting_full_shelf_threshold_and_coefficient_ratio_rounding_source','actual_supporting_passed_trial5','actual_supporting_source_snapshot','actual_supporting_raw_log']:
    p=path(proposal[k]);assert sha(p)==proposal[k]['sha256'];bind(p)
for p in [REQUEST,FIND,ACTUAL,Path(a['log']),CONTEXT,
          Path('/tmp/check-modules-shelf-rounding-independent-foundations30-v1.py'),
          Path('/tmp/run-modules-shelf-rounding-independent-foundations30-v1.py'),
          Path(d['fresh_full29_inventory']['file']),Path(d['fresh_full29_parser_log']['file']),
          Path('/tmp/prepare-modules-shelf-rounded-coefficients-unnumbered-proposal30-v1.py'),
          Path('/tmp/run-modules-shelf-rounded-coefficients-unnumbered-proposal30-preparation-v1.py'),
          Path('/tmp/modules-shelf-rounded-coefficients-unnumbered-proposal30-preparation-actual-v1.json'),
          Path('/tmp/modules-shelf-rounded-coefficients-unnumbered-proposal30-preparation-actual-v1.log'),
          ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean',Path(__file__)]:bind(p)
author=Path('/tmp/modules-shelf-rounded-coefficients-unnumbered-proposal30-preparation-actual-v1.json')
authornative=json.loads(author.read_bytes())
assert type(authornative['actual_exit_code']) is int and authornative['actual_exit_code']==0 and authornative['protection_errors']==[]
def norm(v):
    if isinstance(v,dict):
        z={k:norm(w) for k,w in v.items()}
        if 'file' in v and 'sha256' in v:
            p=path(v);assert sha(p)==v['sha256'] and str(p) in aliases;z.update(aliases[str(p)])
        return z
    if isinstance(v,list):return [norm(w) for w in v]
    return v
peer={'status':'passed_independent_narrow_shelf_rounding_full_literals_and_fresh_full29_parser_review',
    'reviewer':'/root/foundations_recovery28','closed_at_utc':datetime.now(timezone.utc).isoformat(),
    'proposal':bind(REQUEST),'original_full_findings':bind(FIND),'original_review_finished_at_utc':d['finished_at_utc'],
    'actual_reader':bind(ACTUAL),'actual_raw_log':bind(a['log']),
    'reader_helper':bind('/tmp/check-modules-shelf-rounding-independent-foundations30-v1.py'),
    'reader_wrapper':bind('/tmp/run-modules-shelf-rounding-independent-foundations30-v1.py'),
    'actual_author_parser_preparation':bind(author),
    'current_source_original':norm(proposal['source']),'proposed_source_original':norm(proposal['proposed_source']),
    'fresh_independent_full29_inventory':norm(d['fresh_full29_inventory']),
    'fresh_independent_full29_parser_log':norm(d['fresh_full29_parser_log']),
    'both_parser_ROOT_and_OUT_strictly_TMP':True,'exact_forward_and_inverse':True,'all_nodes_tags_attrs_lines_equal':True,
    'changed_literal_keys':d['changed_literal_keys'],
    'all_other555_exercise_texts_other_material_shapes_and28_pages_exact':True,
    'full_current_proposed_exercise17_node1126_and907_921_context_read':True,
    'complete_support29_and_used_exp_Taylor_power_scaling_proof_bodies_read':True,
    'narrow_wording_approved':True,'mathematical_reason':d['mathematical_reason'],
    'supporting_original_genuine29_pass_retained_without_recompilation':True,
    'actual_supporting_passed_trial5':norm(proposal['actual_supporting_passed_trial5']),
    'actual_supporting_source':norm(proposal['actual_supporting_full_shelf_threshold_and_coefficient_ratio_rounding_source']),
    'actual_supporting_raw_log':norm(proposal['actual_supporting_raw_log']),
    'supporting_exact_emitted_warning_count':d['supporting_actual_emitted_warning_count'],
    'whole57_or_whole_exercise_or_whole1126_approval_inferred':False,
    'source_ordinal_reserved':False,'source_applied':False,'all_original_body_and_time_preserved':True,
    'all_original_byte_aliases':aliases,'required_evidence_artifacts_sha256':closed,
    'actual_protected_original_context':bind(CONTEXT),'actual1197_31_five_before_after_unchanged':True,
    'prospective_postfreeze_evidence_not_part_of_frozen29':True,
    'compiler_source_owner_canonical_publication_mutation':False,'coverage_complete':False,'errors':[]}
out=BASE/'modules-shelf-rounding-unnumbered-narrow-full-literal-parser-independent-foundations30-closed-peer-v1.json'
assert not out.exists();out.write_text(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
assert all(not (ROOT/n).is_symlink() and (ROOT/n).resolve().is_relative_to(ROOT) and sha(ROOT/n)==h for n,h in closed.items())
assert all(sha(ROOT/n)==h for n,h in protected.items())
print(json.dumps({'peer':ref(out),'physical_refs':len(closed),'original_aliases':len(aliases),'actual_reader_code':0,'protection_errors':[]}))
