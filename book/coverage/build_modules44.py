"""Build the module ledger using explicit unchanged-literal identity and fresh reviews.

The validated source33 ledger and every original review remain immutable. Changed
whole literals are excluded until a separately timed source44 review approves them.
"""
from pathlib import Path
import collections
import copy
import datetime
import hashlib
import json
import sys

ROOT=Path(__file__).resolve().parents[2]
MAPPING='book/coverage/checks/modules-future19/review-mappings44-v2.json'
SIDE='book/coverage/checks/modules-source44-unchanged-literal-identity-v2.json'

def read(path):return json.loads((ROOT/path).read_text())
def digest(path):return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
def build():
    mapping=read(MAPPING);side=read(SIDE)
    assert mapping['unchanged_identity_sidecar']=={'file':SIDE,'sha256':digest(SIDE)}
    old=read(side['historical_ledger']['preserved'])
    assert digest(side['historical_ledger']['preserved'])==side['historical_ledger']['sha256']
    ledger=copy.deepcopy(old);inv=read('book/coverage/inventory-after-correction44.json')
    assert digest('book/coverage/inventory.json')==mapping['inventory_sha256']==side['current_inventory']['sha256']
    exact={e['key']:e for e in inv['exercises']};units={u['key']:u for u in inv['material_source_units']}
    changed_e={r['key'] for r in side['changed_owned_literals_excluded']['exercises']}
    changed_u={r['key'] for r in side['changed_owned_literals_excluded']['material_source_units']}
    excluded=[];identity_ref={'file':SIDE,'sha256':digest(SIDE),'status':side['status']}
    for e in ledger['exercises']:
        actual=exact[e['inventory_key']]
        if e['inventory_key'] in changed_e:
            excluded.append({'kind':'changed_exercise_parent','key':e['inventory_key'],'original_claim_ids':[c['id'] for c in e['claims']],'historical_ledger':side['historical_ledger']})
            e['claims']=[dict(id=e['inventory_key']+'::corrected44-pending-whole',statement_in_prose=actual['source_text'],kind='changed_whole_exercise_requires_fresh_source_review',status='pending',lean_declarations=[],hypotheses=[],correspondence='',remaining_gaps=['The complete corrected exercise requires a fresh source44 review; original33 decisions remain historical.'],source_unit_keys=[])]
            e['status']='pending';e.pop('independent_whole_source_review',None)
        else:e['source44_unchanged_literal_identity']=identity_ref
        e['source_sha256']=actual['source_sha256'];e['source_text_sha256']=actual['text_sha256']
    kept=[]
    for c in ledger['material_claims']:
        keys=set(c['source_unit_keys']);changed=keys&changed_u
        if changed and not any(c['id']==k+'::claim-review' for k in changed):
            excluded.append({'kind':'component_bound_to_changed_literal','id':c['id'],'source_unit_keys':sorted(keys),'historical_ledger':side['historical_ledger']});continue
        if changed:
            k=next(k for k in changed if c['id']==k+'::claim-review')
            c.update(statement_in_prose=units[k]['source_text'],status='pending',kind='changed_whole_material_requires_fresh_source_review',lean_declarations=[],hypotheses=[],correspondence='',remaining_gaps=['The complete corrected physical unit requires a fresh source44 review; original33 decisions remain historical.'])
            c.pop('independent_source_review',None)
        else:c['source44_unchanged_literal_identity']=identity_ref
        kept.append(c)
    ledger['material_claims']=kept
    exercise_rows={e['inventory_key']:e for e in ledger['exercises']};whole={c['id']:c for c in kept}
    for review in mapping['reviews']:
        ref=review['review'];original=read(ref['file']);assert digest(ref['file'])==ref['sha256'] and original['reviewed_at_utc']==ref['original_review_time']
        for e in review['exercises']:
            actual=exact[e['key']];assert actual['text_sha256']==e['text_sha256']
            row=exercise_rows[e['key']]
            row['claims']=[dict(id=e['key']+'::source44-independent-whole',statement_in_prose=actual['source_text'],kind='independently_reviewed_whole_exercise',status='proved',lean_declarations=e['lean_declarations'],hypotheses=e['hypotheses'],correspondence=e['reason'],remaining_gaps=[],source_unit_keys=[],independent_source_review=ref,scope_limits=review['limits'])]
            row['status']='complete_math';row['independent_whole_source_review']=ref
        for u in review['material_units']:
            actual=units[u['key']];assert actual['text_sha256']==u['text_sha256'] and actual['source_sha256']==u['source_sha256']
            c=whole[u['key']+'::claim-review'];c.update(statement_in_prose=actual['source_text'],status=u['status'],kind=u['kind'],lean_declarations=u['lean_declarations'],hypotheses=u['hypotheses'],correspondence=u['reason'],remaining_gaps=[],independent_source_review=ref,scope_limits=review['limits'])
    ledger.update(generated_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_sha256={p:inv['source_sha256'][p] for p in old['scope_pages']},current_inventory='book/coverage/inventory-after-correction44.json',current_inventory_sha256=digest('book/coverage/inventory-after-correction44.json'))
    ledger['chapter_fragment_sha256']={p:digest(p) for p in old['chapter_fragment_sha256']}
    ledger['inventory_identity_rebase44']={'identity_sidecar':identity_ref,'historical_ledger':side['historical_ledger'],'changed_original_claims_excluded_from_reuse':excluded,'fresh_mapping':{'file':MAPPING,'sha256':digest(MAPPING)}}
    ledger['reviewed_work_integration19_source33_preserved']={'historical_ledger':side['historical_ledger'],'original_review_bodies_and_times_preserved':side['original_semantic_review_bodies_times_preserved']}
    ledger['reviewed_work_integration19']={'mapping':MAPPING,'mapping_sha256':digest(MAPPING),'canonical_path_aliases':mapping['canonical_path_aliases'],'exact_reviews':[r['review'] for r in mapping['reviews']],'scope':'Fresh44 whole decisions and exact unchanged33 literal identity; original semantic bodies/times remain historical byte-exact.'}
    ledger['counts']={'exercises':len(ledger['exercises']),'exercise_status':dict(collections.Counter(e['status'] for e in ledger['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status'] for e in ledger['exercises'] for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status'] for c in ledger['material_claims'])),'new_declarations':len(ledger['declarations'])}
    ledger['remaining_research_theorem_families']=['Remaining claims are the exact pending source44 exercise/material clauses in this ledger and its generated gap manifest. Historical broad family summaries are preserved in the source33 ledger and are not used as current completion evidence.']
    from modules_binding19_source44 import check_bindings
    guard=check_bindings(ROOT,ledger,inv,old,side,mapping)
    gp='book/coverage/checks/modules-source44-bindings19-v2.json'
    (ROOT/gp).write_text(json.dumps(guard,indent=2,ensure_ascii=False)+'\n')
    ledger['current_identity_binding_validation']={'file':gp,'sha256':digest(gp),'status':guard['status'],'validator':'book/coverage/modules_binding19_source44.py','validator_sha256':digest('book/coverage/modules_binding19_source44.py')}
    (ROOT/'book/coverage/modules.json').write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(ledger['counts'],indent=2))
    return ledger

if __name__=='__main__':build()
