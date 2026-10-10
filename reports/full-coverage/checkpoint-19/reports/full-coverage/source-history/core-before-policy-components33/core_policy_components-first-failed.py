"""Integrate independently reviewed policy components with literal gaps retained."""
import hashlib
import json
from pathlib import Path

REVIEWS=(
    'policy-penalty-barrier-9-4-source-components-review-v1.json',
    'policy-benchmark-9-5-source-components-review19-v1.json',
)


def integrate(root, inventory, sha, add, mapping, direct_material, component_material):
    alias_path=root/'book/coverage/checks/core-future19-evidence/policy-penalty-review-original-tmp-aliases.json'
    aliases=json.loads(alias_path.read_text())['aliases']
    def resolve(name):
        if name.startswith('/tmp/'):
            row=aliases[name]
            target=root/row['file']
            assert hashlib.sha256(target.read_bytes()).hexdigest()==row['sha256']
            return target
        target=(root/name).resolve()
        assert target.is_relative_to(root.resolve()),name
        return target
    def digest(name):
        return hashlib.sha256(resolve(name).read_bytes()).hexdigest()
    units={u['key']:u for u in inventory['material_source_units']}
    exercises={e['key']:e for e in inventory['exercises']}
    proof_sources={}
    for filename in REVIEWS:
        path='book/coverage/checks/'+filename
        review=json.loads((root/path).read_text())
        assert review['inventory_sha256']==sha('book/coverage/inventory.json')==digest(review['inventory'])
        assert review['missing_clauses']
        for source,expected in review['source_sha256'].items():
            assert digest(source)==inventory['source_sha256'][source]==expected
        for source,expected in review['proof_source_sha256'].items():
            assert digest(source)==expected
            proof_sources[source]=expected
        seen=set()
        for evidence in review['actual_standalone_evidence']:
            name=evidence['compiler_manifest']
            assert digest(name)==evidence['compiler_manifest_sha256']
            actual=json.loads(resolve(name).read_text())
            assert actual==evidence.get('raw_execution_record',evidence.get('record'))
            assert actual['exit_code']==evidence['actual_exit_code']==0
            assert actual['source_sha256_before']==actual['source_sha256_after']==digest(actual['source'])
            assert actual['source_sha256_after']==review['proof_source_sha256'][actual['source']]
            assert digest(actual['log'])==actual['log_sha256']
            seen.add(actual['source'])
        assert seen==set(review['proof_source_sha256'])
        for source in review.get('primary_source_checks',[]):
            assert digest(source['path'])==source['sha256']
        for record in review['records']:
            key=record['exercise_key'];actual=exercises[key]
            assert key in {'policy-optimization.html::exercise-19','policy-optimization.html::exercise-20'}
            assert actual['text_sha256']==record['exercise_text_sha256']
            assert record['missing_clauses']
            clauses=record.get('components',record.get('reviewed_clauses'))
            assert clauses and all(c['status']=='approved_precise_component' and not c['missing_clauses'] and c['lean_declarations'] and c['per_clause_reason'] for c in clauses)
            declared=list(dict.fromkeys(n for c in clauses for n in c['lean_declarations']))
            assumptions=list(dict.fromkeys(h for c in clauses for h in c['hypotheses']))
            add(key,declared,record['per_exercise_reason'],assumptions,record['missing_clauses'])
            mapping[key]['source_review']=dict(file=path,sha256=sha(path),component_ids=[c['id'] for c in clauses],limits=review['limits'])
        for record in review['material_units']:
            key=record['source_unit_key'];unit=units[key]
            assert unit['source_sha256']==record['source_sha256']
            assert unit['text_sha256']==record['unit_text_sha256'] and unit['source_text']==record['source_text']
            assert record['per_unit_reason'] and record['lean_declarations']
            if record['material_status']=='proved':
                assert record['review_status']=='approved_complete_source' and not record['missing_clauses'] and key not in direct_material
                direct_material[key]=dict(record=record,path=path,review_sha256=sha(path))
            else:
                assert record['material_status']=='pending' and record['missing_clauses']
                assumptions=record.get('hypotheses',list(dict.fromkeys(h for r in review['records'] for c in r.get('components',r.get('reviewed_clauses')) for h in c['hypotheses'])))
                # Keep the full answer pending; the extra precise component claim
                # records its already reviewed mathematics without closing it.
                normalized=dict(record)
                normalized.setdefault('approved_component_ids',[c['id'] for r in review['records'] for c in r.get('components',r.get('reviewed_clauses'))])
                component_material.append(dict(record=normalized,path=path,review_sha256=sha(path),review_name=Path(filename).stem,hypotheses=assumptions))
    return proof_sources
