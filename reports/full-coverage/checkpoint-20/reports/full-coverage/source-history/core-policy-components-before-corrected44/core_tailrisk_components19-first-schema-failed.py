"""Bind the actual CMDP8.5 tail proof while retaining its printed precision gap."""
import json


def integrate(root, inventory, sha, add, mapping, direct_material, component_material):
    path='book/coverage/checks/cmdp-tailrisk-8-5-original44-source-components-review19-v1.json'
    review=json.loads((root/path).read_text())
    assert review['status']=='independent_original44_tailrisk_components_approved_whole_pending_precision'
    assert review['inventory_sha256']==sha(review['inventory'])==sha('book/coverage/inventory.json')
    assert review['missing_clauses']
    for name,h in review['source_sha256'].items():assert sha(name)==inventory['source_sha256'][name]==h
    for name,h in review['proof_source_sha256'].items():assert sha(name)==h
    primary=review['primary_source_check'];assert sha(primary['path'])==primary['sha256']
    seen=set()
    for evidence in review['actual_standalone_and_named_evidence']:
        name=evidence['compiler_manifest'];assert sha(name)==evidence['compiler_manifest_sha256']
        actual=json.loads((root/name).read_text());assert actual==evidence['record']
        assert actual['exit_code']==evidence['actual_exit_code']==0
        assert actual['source_sha256_before']==actual['source_sha256_after']==sha(actual['source'])==review['proof_source_sha256'][actual['source']]
        assert sha(actual['log'])==actual['log_sha256']==evidence['raw_log_sha256']
        seen.add(actual['source'])
    assert seen==set(review['proof_source_sha256'])
    for evidence in review['imported_actual_evidence']:
        name=evidence['record'];assert sha(name)==evidence['record_sha256']
        actual=json.loads((root/name).read_text());assert actual['exit_code']==evidence['actual_exit_code']==0
        assert sha(evidence['source'])==evidence['source_sha256']
        assert sha(evidence['raw_log'])==evidence['raw_log_sha256']
    units={r['key']:r for r in inventory['material_source_units']}
    exercise=next(r for r in inventory['exercises'] if r['key']=='cmdp.html::exercise-20')
    assert len(review['records'])==1
    record=review['records'][0];assert record['exercise_key']==exercise['key']
    assert record['exercise_text_sha256']==exercise['text_sha256'] and record['exercise_text']==exercise['source_text']
    assert not record['whole_exercise_approved'] and record['missing_clauses']
    clauses=record['components'];assert clauses and clauses==record['reviewed_clauses']
    for c in clauses:
        assert c['review_status']=='approved_precise_source_component' and c['lean_declarations'] and c['per_clause_reason']
        assert isinstance(c['hypotheses'],list) and not c['missing_clauses']
    names=list(dict.fromkeys(n for c in clauses for n in c['lean_declarations']))
    add(exercise['key'],names,record['per_exercise_reason'],record['hypotheses'],record['missing_clauses'])
    mapping[exercise['key']]['source_review']=dict(file=path,sha256=sha(path),component_ids=[c['id'] for c in clauses],limits=review['limits'])
    approved=set();pending=set()
    for r in review['material_units']:
        key=r['source_unit_key'];u=units[key]
        assert r['unit_text_sha256']==u['text_sha256'] and r['source_text']==u['source_text'] and r['source_sha256']==u['source_sha256']
        assert r['line']==u['line'] and r['locator']==u['locator'] and r['lean_declarations'] and r['per_unit_reason']
        if r['material_status']=='proved':
            assert r['review_status']=='approved_complete_source' and not r['missing_clauses'] and key not in direct_material
            direct_material[key]=dict(record=r,path=path,review_sha256=sha(path));approved.add(key)
        else:
            assert r['material_status']=='pending' and r['missing_clauses'];pending.add(key)
            normalized=dict(r,approved_component_ids=[c['id'] for c in r['reviewed_clauses']])
            component_material.append(dict(record=normalized,path=path,review_sha256=sha(path),review_name='cmdp-tailrisk-8-5-original44-v1',hypotheses=r['hypotheses']))
    assert approved=={'cmdp.html::node-1123','cmdp.html::node-1127','cmdp.html::node-1128'} and pending=={'cmdp.html::node-1129'}
    return review['proof_source_sha256']
