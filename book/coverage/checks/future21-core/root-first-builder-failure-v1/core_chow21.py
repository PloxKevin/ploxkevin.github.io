"""Integrate the fresh, independently approved full current48 Chow exercise."""
import json
from pathlib import Path
from lean_names import declarations
REVIEW='book/coverage/checks/chow115-current48-whole-independent-applied-source-review21-v1.json'
REVIEW_SHA256='151b94ffb21b02ff000198924b03faa6b6ccb998964a431cc7519605cb73c98b'
def integrate(root,inventory,sha,add,mapping,direct_material):
    assert sha(REVIEW)==REVIEW_SHA256
    review=json.loads((root/REVIEW).read_text())
    assert review['status']=='independent_whole_source_review_passed' and review['reviewer']=='/root/applied_next'
    assert review['inventory_sha256']==sha(review['inventory'])==sha('book/coverage/inventory.json')
    for source,digest in review['source_sha256'].items(): assert sha(source)==digest==inventory['source_sha256'][source]
    aliases={row['original_path']:row for row in review['original_named_path_aliases']}
    def canonical(name):
        path=Path(name)
        if path.is_absolute() and str(path).startswith('/tmp/'):
            row=aliases[name];assert sha(row['canonical_path'])==row['sha256'];return row['canonical_path']
        if path.is_absolute(): return str(path.resolve().relative_to(root.resolve()))
        assert (root/path).resolve().is_relative_to(root.resolve());return name
    exported=set()
    assert len(review['proof_source_sha256'])==9
    for source,digest in review['proof_source_sha256'].items():
        assert sha(source)==digest
        exported.update(d['name'] for d in declarations((root/source).read_text()))
    seen=set()
    for evidence in review['actual_standalone_and_named_evidence']:
        name=evidence['record'];assert sha(name)==evidence['record_sha256']
        actual=json.loads((root/name).read_text());assert actual==evidence['raw_actual_execution'] and actual['exit_code']==0
        source=evidence['source'];assert canonical(actual['source'])==source
        assert actual['source_sha256_before']==actual['source_sha256_after']==evidence['source_sha256']==sha(source)==review['proof_source_sha256'][source]
        assert canonical(actual['log'])==evidence['canonical_log']
        assert sha(evidence['canonical_log'])==actual['log_sha256']==evidence['canonical_log_sha256']
        command=actual.get('command',actual.get('actual_command'))
        if evidence['kind']=='actual_standalone':
            assert command==['lake','env','lean',str(Path(source).relative_to('verification/lean'))]
            kind='standalone'
        elif evidence['kind']=='actual_named-build':
            assert command==['lake','build','SafeLearning.'+Path(source).stem]
            kind='named'
        else:
            assert evidence['kind']=='actual_named_lean_output_build'
            assert command[:4]==['lake','env','lean','-o'] and canonical(command[-1])==source
            assert command[4]==actual['olean'] and Path(command[4]).name==Path(source).stem+'.olean' and actual['olean_sha256']
            kind='named'
        assert (source,kind) not in seen;seen.add((source,kind))
    assert len(review['actual_standalone_and_named_evidence'])==18 and seen=={(s,k) for s in review['proof_source_sha256'] for k in ('standalone','named')}
    primary=review['primary_attribution'];assert sha(primary['local_text'])==primary['local_text_sha256'] and primary['official_source']=='https://arxiv.org/pdf/1805.07708'
    assert sha(review['proof_manifest'])==review['proof_manifest_sha256']
    assert len(review['records'])==1
    record=review['records'][0];key='lyapunov-mpc.html::exercise-20'
    exercise=next(x for x in inventory['exercises'] if x['key']==key)
    assert record['exercise_key']==key and record['entire_inventory_record']==exercise
    assert record['exercise_text']==exercise['source_text'] and record['exercise_text_sha256']==exercise['text_sha256'] and record['source_sha256']==exercise['source_sha256']
    assert record['whole_exercise_approved'] and record['independent_whole_source_review_passed'] and record['review_status']=='approved_complete_source' and not record['missing_clauses']
    groups=review['approved_mathematical_groups'];assert groups==record['components'] and len(groups)==9
    names=list(dict.fromkeys(n for group in groups for n in group['lean_declarations']))
    hypotheses=list(dict.fromkeys(h for group in groups for h in group['hypotheses']))
    assert len(names)==65 and set(names)==set(record['lean_declarations']) and set(names)<=exported
    for group in groups:
        assert group['review_status']=='approved_precise_source_component' and group['per_component_reason'] and group['hypotheses'] and group['lean_declarations'] and not group['missing_clauses']
    assert len(record['reviewed_clauses'])==9
    for clause in record['reviewed_clauses']:
        assert clause['component'] in {g['id'] for g in groups} and clause['per_component_reason'] and not clause['missing_clauses']
    add(key,names,' '.join(g['statement'] for g in groups),hypotheses,[])
    mapping[key]['source_review']=dict(file=REVIEW,sha256=REVIEW_SHA256,component_ids=[g['id'] for g in groups],limits=review['limits'])
    units={x['key']:x for x in inventory['material_source_units']}
    assert {row['source_unit_key'] for row in review['material_units']}=={'lyapunov-mpc.html::node-'+str(n) for n in (1408,1412,1414,1417,1419)}
    for row in review['material_units']:
        key=row['source_unit_key'];unit=units[key]
        assert row['entire_inventory_record']==unit
        for field,actual in [('source','source'),('source_sha256','source_sha256'),('unit_text_sha256','text_sha256'),('source_text','source_text'),('line','line'),('locator','locator')]: assert row[field]==unit[actual]
        assert row['material_status']=='proved' and row['review_status']=='approved_complete_source' and not row['missing_clauses'] and row['per_unit_reason']
        assert row['lean_declarations'] and set(row['lean_declarations'])<=exported and key not in direct_material
        direct_material[key]=dict(record=row,path=REVIEW,review_sha256=REVIEW_SHA256)
    return review['proof_source_sha256']
