"""Freeze the Source92 candidate runtime and rebase unchanged reviewed scopes."""
import argparse
import copy
import importlib.util
import os
from pathlib import Path
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
sys.path.insert(0,str(ROOT/'book/coverage/source91-piece01'))
import common as c

BASE='book/solutions/releases/source92-opening-v1'
PLAN=BASE+'/plan-v1.json'
PRIOR='reports/full-coverage/runtime-source91-piece02-v1'
RUNTIME='reports/solution-review/runtime-source92-piece02-v1'
INVENTORY=BASE+'/source92-inventory/inventory.json'
PREPARATION=BASE+'/current-runtime-preparation-v1.json'
AUDIT=RUNTIME+'/reports/lean-verification/verification.json'


def prepare():
    plan=h.read(PLAN);audit=h.read(PRIOR+'/reports/lean-verification/verification.json')
    assert audit['status']=='passed' and audit['proof_file_count']==1272 and audit['theorem_count']==11522
    expected={**audit['proof_sha256'],**audit['project_sha256']}
    expected['book/coverage/lean_names.py']=h.ref(PRIOR+'/book/coverage/lean_names.py')['sha256']
    for name,digest in expected.items():
        origin=PRIOR+'/'+name;assert h.ref(origin)['sha256']==digest
        target=ROOT/RUNTIME/name;target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():assert h.ref(RUNTIME+'/'+name)['sha256']==digest
        else:os.link(h.path(origin),target)
    for name,digest in plan['site_after_sha256'].items():
        origin=BASE+'/candidates/'+name;assert h.ref(origin)['sha256']==digest
        c.put(RUNTIME+'/'+name,h.path(origin).read_bytes())
    for part in ['build','packages']:
        target=ROOT/RUNTIME/'verification/lean/.lake'/part
        origin=ROOT/'verification/lean/.lake'/part
        target.parent.mkdir(parents=True,exist_ok=True)
        if target.is_symlink():assert target.resolve()==origin.resolve()
        else:
            assert not target.exists()
            target.symlink_to(origin.resolve(),target_is_directory=True)
    assert {p.name for p in (ROOT/RUNTIME/'verification/lean/SafeLearning').iterdir()}=={Path(n).name for n in audit['proof_sha256']}
    if not h.path(INVENTORY).exists():
        sys.path.insert(0,str(ROOT/'book'))
        spec=importlib.util.spec_from_file_location('recovery_source92_inventory',ROOT/'book/inventory_claims.py')
        inv=importlib.util.module_from_spec(spec);spec.loader.exec_module(inv)
        with tempfile.TemporaryDirectory(prefix='.inventory-recovery-',dir=ROOT/BASE) as directory:
            inv.ROOT=ROOT/BASE/'candidates';inv.OUT=Path(directory);inv.inventory()
            h.put(INVENTORY,(Path(directory)/'inventory.json').read_bytes())
    inventory=h.read(INVENTORY)
    assert inventory['status']=='inventory_only_no_coverage_claim' and inventory['counts']['exercises']==556
    assert all(inventory['source_sha256'][n]==digest for n,digest in plan['site_after_sha256'].items() if n.endswith('.html'))
    h.json_put(PREPARATION,{'status':'prepared_exact_source92_selected1272_runtime_no_completion_credit',
        'runtime':RUNTIME,'plan':h.ref(PLAN),'prior_audit':h.ref(PRIOR+'/reports/lean-verification/verification.json'),
        'proof_sha256':audit['proof_sha256'],'site_sha256':plan['site_after_sha256'],
        'inventory':h.ref(INVENTORY),'counts':inventory['counts'],
        'helper':h.ref(BASE+'/prepare_current_scope.py'),'caches_copied':False})
    print({'status':'prepared','files':1272,'theorems':11522,'exercises':556,'material_units':inventory['counts']['material_source_units']})


def rebase():
    plan,audit,inventory=map(h.read,[PLAN,AUDIT,INVENTORY])
    assert audit['status']=='passed' and audit['proof_file_count']==1272 and audit['theorem_count']==11522
    assert audit['source_sha256']==plan['site_after_sha256']
    assert audit['proof_sha256']==h.read(PREPARATION)['proof_sha256']
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in audit['axiom_dependencies'].values())
    current_raw=h.path(BASE+'/candidates/SafeLearning/landscape.html').read_bytes()
    old_inventory=h.read('book/solutions/releases/source91-v1/source91-inventory/inventory.json')
    key='landscape.html::exercise-19'
    old_ex=next(r for r in old_inventory['exercises'] if r['key']==key)
    new_ex=next(r for r in inventory['exercises'] if r['key']==key)
    assert old_ex['source_text']==new_ex['source_text'] and old_ex['text_sha256']==new_ex['text_sha256']
    old_baseline=h.read(BASE+'/baseline-source91/pages/landscape.html.json')
    old_row=next(r for r in old_baseline['exercises'] if r['inventory_key']==key)
    doc=h.Document(current_raw);node=doc.exercises()[old_row['ordinal']-1]
    scope=doc.piece(node.start,node.end)
    assert scope['sha256']==old_row['exercise']['sha256']
    indexed={r['key']:r for r in inventory['material_source_units']}
    results=[]
    for filename,unit_field in [('book/coverage/source91-piece01/ledger-v1.json','complete_leaf_material_units'),
                                ('book/coverage/source91-piece02/ledger-v1.json','source_units')]:
        original=h.read(filename);old_raw=h.path(original['reader_source']['file']).read_bytes()
        assert h.ref(original['reader_source']['file'])==original['reader_source']
        new=copy.deepcopy(original);mapping={}
        for unit in new[unit_field]:
            exact=old_raw[unit['start_byte']:unit['end_byte']]
            assert h.sha(exact)==unit['exact_html_sha256']
            found=[(i,n) for i,n in enumerate(doc.nodes,1) if n.start>=node.start and n.end<=node.end
                   and doc.raw[doc.byte(n.start):doc.byte(n.end)]==exact]
            assert len(found)==1,(unit['key'],len(found))
            ordinal,matched=found[0]
            new_key='landscape.html'+('#'+matched.attrs['id'] if matched.attrs.get('id') else '::node-'+str(ordinal))
            current=indexed[new_key]
            assert current['text_sha256']==unit['exact_text_sha256']
            mapping[unit['key']]=new_key
            unit.update(key=new_key,material_unit_key=new_key,start_byte=doc.byte(matched.start),
                        end_byte=doc.byte(matched.end),line=doc.range(matched.start,matched.end)['start_line'])
        for claim in new['claims']:
            for field in ['source_unit_key','material_unit_key']:
                if field in claim:claim[field]=mapping[claim[field]]
        fragment_field='exact_part_i_fragment' if 'exact_part_i_fragment' in new else 'fragment'
        fragment=original[fragment_field];raw=old_raw[fragment['start_byte']:fragment['end_byte']]
        a=scope['range']['start_byte'];b=scope['range']['end_byte']
        assert current_raw[a:b].count(raw)==1
        start=current_raw.index(raw,a,b)
        new[fragment_field]={'start_byte':start,'end_byte':start+len(raw),'sha256':h.sha(raw)}
        new.update(source_version='Source92',inventory=h.ref(INVENTORY),reader_source=h.ref(BASE+'/candidates/SafeLearning/landscape.html'),
            audit=h.ref(AUDIT),previous_exact_source_ledger=h.ref(filename),
            rebase={'status':'passed_exact_unchanged_whole_exercise_and_reviewed_leaf_bytes',
                    'old_exercise_text_sha256':old_ex['text_sha256'],'new_exercise_text_sha256':new_ex['text_sha256'],
                    'whole_exercise_html_sha256':scope['sha256'],'source_unit_key_mapping':mapping,
                    'new_completion_credit':0,'independent_previous_correspondence_retained':True})
        # Bind the canonical path while retaining the frozen actual source object.
        new['reader_source_snapshot']=new['reader_source']
        new['reader_source']={'file':'SafeLearning/landscape.html','sha256':audit['source_sha256']['SafeLearning/landscape.html']}
        target=BASE+'/formal-rebase-piece'+str(original['piece'])+'-v1.json'
        h.json_put(target,new);results.append(h.ref(target))
    h.json_put(BASE+'/formal-rebase-v1.json',{'status':'passed_exact_source92_piece01_piece02_rebase',
        'inventory':h.ref(INVENTORY),'audit':h.ref(AUDIT),'ledgers':results,
        'counts':{'proved_mathematical_clauses':27,'complete_leaf_units':12,'complete_whole_exercises':0},
        'exercise_status':'partial','part_ii_status':'partial_numerical_warning_leaf_pending',
        'source92_opening_rewrite_formal_credit':0,'full_formal_coverage_complete':False})
    print({'status':'rebased_exact_unchanged_scopes','proved_clauses':27,'complete_leaves':12,'whole_exercise':'partial'})


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('command',choices=['prepare','rebase']);args=p.parse_args()
    prepare() if args.command=='prepare' else rebase()
