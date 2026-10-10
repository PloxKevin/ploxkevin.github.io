"""Apply exact peer review decisions while preserving historical JSON bodies."""
import hashlib
import json
from pathlib import Path
from functools import lru_cache

ALIAS='book/coverage/checks/modules-future19/path-aliases33-v3.json'
MAPPINGS='book/coverage/checks/modules-future19/review-mappings33-v4.json'

@lru_cache(maxsize=4)
def alias_rows(root):
    return json.loads((root/ALIAS).read_text())["aliases"]

def resolve(root, path):
    value=str(path)
    if value.startswith('/tmp/'):
        aliases=alias_rows(root)
        if value not in aliases:
            raise AssertionError(('unresolved historical evidence path',value))
        value=aliases[value]['path']
    target=root/value
    assert target.is_relative_to(root) and ".." not in target.parts,value
    return target

def digest(root,path):
    return hashlib.sha256(resolve(root,path).read_bytes()).hexdigest()

def apply_reviews(root, inventory, exercises, material):
    data=json.loads((root/MAPPINGS).read_text())
    assert data['inventory_sha256']==digest(root,'book/coverage/inventory.json')
    assert not data['normalization_errors']
    assert digest(root,data['canonical_path_aliases']['file'])==data['canonical_path_aliases']['sha256']
    units={u['key']:u for u in inventory['material_source_units']}
    exact={e['key']:e for e in inventory['exercises']}
    exercise_rows={e['inventory_key']:e for e in exercises}
    whole_claims={c['id']:c for c in material}
    def new_claim(id,statement,names,status,kind,hypotheses,reason,gaps,keys,ref,limits):
        return dict(id=id,statement_in_prose=statement,kind=kind,lean_declarations=names,status=status,
          hypotheses=hypotheses,correspondence=reason,remaining_gaps=gaps,source_unit_keys=keys,
          independent_source_review=ref,scope_limits=limits)
    used=[]
    for ri,review in enumerate(data['reviews']):
        ref=review['review'];assert digest(root,ref['file'])==ref['sha256']
        original=json.loads(resolve(root,ref['file']).read_text())
        assert original.get('reviewed_at_utc')==ref['original_review_time']
        assert original.get('reviewer')==ref['reviewer']
        used.append(ref)
        for e in review['exercises']:
            actual=exact[e['key']];row=exercise_rows[e['key']]
            assert actual['text_sha256']==e['text_sha256']
            # Replace earlier tentative decomposition with the exact reviewed
            # whole literal and the independently reviewed precise clauses.
            claims=[new_claim(e['key']+'::review19-whole',actual['source_text'],e['lean_declarations'],'proved','whole_exercise_source',e['hypotheses'],e['reason'],[],[],ref,review['limits'])]
            for ci,c in enumerate(e['components']):
                names=c.get('lean_declarations',c.get('declarations',[]))
                if not names:continue
                reason=c.get('per_component_reason',c.get('per_clause_reason',c.get('reason','')))
                claims.append(new_claim(e['key']+'::review19-component-'+str(ci+1),c.get('source_clause',c.get('statement',reason)),names,'proved','precise_source_component',c.get('hypotheses',[]),reason or e['reason'],[],[],ref,review['limits']))
            row.update(claims=claims,status='complete_math',independent_whole_source_review=ref)
        for u in review['material_units']:
            actual=units[u['key']];assert actual['text_sha256']==u['text_sha256'] and actual['source_sha256']==u['source_sha256']
            id=u['key']+'::claim-review';c=whole_claims[id]
            c.update(status=u['status'],kind=u['kind'],lean_declarations=u['lean_declarations'],hypotheses=u['hypotheses'],correspondence=u['reason'],remaining_gaps=u['missing_clauses'],independent_source_review=ref,scope_limits=review['limits'])
        for ci,c in enumerate(review['components']):
            material.append(new_claim('modules::review19-'+str(ri+1)+'-'+str(ci+1),c['statement'],c['lean_declarations'],'proved','precise_source_component',c['hypotheses'],c['reason'],[],c['source_unit_keys'],ref,review['limits']))
    return dict(mapping=MAPPINGS,mapping_sha256=digest(root,MAPPINGS),canonical_path_aliases=data['canonical_path_aliases'],exact_reviews=used,scope='Exact literal full and partial source decisions only; historical review bodies and times preserved.')
