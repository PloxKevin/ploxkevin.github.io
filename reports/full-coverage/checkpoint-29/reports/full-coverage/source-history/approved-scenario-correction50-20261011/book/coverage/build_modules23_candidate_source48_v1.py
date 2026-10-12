"""Build a new isolated seven-practice NN23 candidate from exact reviewed inputs.

Only unique candidate/guard files are written. Live checkpoint22 ledgers,
selection, source HTML, prior proof/review bodies and compiler records are held.
"""
from pathlib import Path
from datetime import datetime, timezone
import copy, json, hashlib, collections, re
from lean_names import declarations

ROOT=Path(__file__).resolve().parents[2]
BASE='book/coverage/checks/modules-future23/source48'
INPUT=BASE+'/nn-seven-practices-input-bindings-v2.json'
INPUT_SHA='7b3627e722c30c988e3049e2bcebc83dd80fddcc7aba67d45e94ef3880cf46fb'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def put(n,d):
    p=ROOT/n;assert not p.exists(),n
    p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')

def build():
    assert sha(INPUT)==INPUT_SHA
    inp=read(INPUT)
    inv=read(inp['inventory']);assert sha(inp['inventory'])==inp['inventory_sha256']==sha('book/coverage/inventory.json')
    es={r['key']:r for r in inv['exercises']};us={r['key']:r for r in inv['material_source_units']}
    baseline=inp['baseline22_module_ledger'];live=inp['baseline22_live_module_ledger']
    assert sha(baseline['file'])==baseline['sha256']==sha(live['file'])==live['sha256']
    old=read(baseline['file']);out=copy.deepcopy(old)
    for n,h in inp['protected_owner_and_html_sha256'].items():assert sha(n)==h,n
    aliasref=inp['canonical_path_aliases'];assert sha(aliasref['file'])==aliasref['sha256']
    aliases=read(aliasref['file'])['aliases']
    for a in aliases.values():assert sha(a['path'])==a['sha256']
    el={r['inventory_key']:r for r in out['exercises']};ul={r['id']:r for r in out['material_claims']}
    mapped=[];mapped_units={};all_names=[];new_paths=[];review_refs=[];new_imports={}
    for proof in inp['proof_files']:
        source=proof['source'];assert sha(source)==proof['sha256']
        ref=proof['original_review'];assert sha(ref['path'])==ref['sha256']
        rv=read(ref['path']);assert rv['reviewed_at_utc']==ref['original_review_time']
        scope=rv.get('scope',rv.get('limits',[]));assert isinstance(scope,list)
        reviewref={'file':ref['path'],'sha256':ref['sha256'],'reviewer':ref['reviewer'],'original_review_time':ref['original_review_time']}
        review_refs.append(reviewref)
        for e in rv['records']:
            k=e['exercise_key'];assert k not in mapped
            entire=e.get('entire_inventory_record',rv.get('entire_exercise_inventory_record'))
            assert entire==es[k],k
            assert e['exercise_text_sha256']==es[k]['text_sha256']
            assert e['whole_exercise_approved'] and e['independent_whole_source_review_passed'] and e['missing_clauses']==[]
            row=el[k];assert row['status']=='pending'
            retained=[c for c in row['claims'] if c['status'] in ('proved','not_a_formal_claim')]
            row['claims']=retained+[{'id':k+'::source48-independent-whole23','statement_in_prose':es[k]['source_text'],
                'kind':'independently_reviewed_whole_exercise','status':'proved','lean_declarations':e['lean_declarations'],
                'hypotheses':e['hypotheses'],'correspondence':e['per_exercise_reason'],'remaining_gaps':[],
                'source_unit_keys':[],'independent_source_review':reviewref,'scope_limits':scope}]
            row['status']='complete_math';row['independent_whole_source_review']=reviewref;mapped.append(k)
        for u in rv['material_units']:
            k=u['source_unit_key'];assert u['entire_inventory_record']==us[k]
            assert u['unit_text_sha256']==us[k]['text_sha256'] and u['missing_clauses']==[] and u['whole_unit_approved']
            status={'proved':'proved','nonformal':'not_a_formal_claim','not_a_formal_claim':'not_a_formal_claim','not_formalizable':'not_a_formal_claim'}[u['material_status']]
            if k in mapped_units:
                assert k=='nn-in-the-loop.html::node-998' and status=='not_a_formal_claim' and not u['lean_declarations']
                target=ul[k+'::claim-review'];assert target['status']==status and not target['lean_declarations']
                target.setdefault('additional_independent_source_reviews',[]).append(reviewref)
                target.setdefault('additional_independent_unit_reasons',[]).append(u['per_unit_reason'])
                mapped_units[k].append(reviewref)
                continue
            ul[k+'::claim-review'].update(statement_in_prose=us[k]['source_text'],status=status,
                kind='independently_reviewed_mathematical_source_unit' if status=='proved' else 'instruction_or_navigation',
                lean_declarations=u['lean_declarations'],hypotheses=u['hypotheses'],correspondence=u['per_unit_reason'],
                remaining_gaps=[],independent_source_review=reviewref,scope_limits=scope)
            mapped_units[k]=[reviewref]
        text=(ROOT/source).read_text()
        names=[r['name'] for r in declarations(text) if r['kind'] in ('theorem','lemma')]
        assert names==proof['public_declarations'] and source not in out['proof_files']
        paired=proof['actual_paired_records'];assert len(paired)==2
        for pair in paired:
            actualref=pair['actual_record'];assert sha(actualref['path'])==actualref['sha256']
            a=read(actualref['path']);assert a['actual_exit_code']==0 and a['source_unchanged'] is True
            assert a['source_sha256_before']==a['source_sha256_after']==sha(source)
            assert a['source']==a['lean_file']==source
            assert sha(pair['raw_log']['path'])==pair['raw_log']['sha256']==a['log_sha256']
            assert sha(pair['source_snapshot']['path'])==pair['source_snapshot']['sha256']==sha(source)
            assert aliases[a['log']]['path']==pair['raw_log']['path']
            assert aliases[a['source_snapshot']]['path']==pair['source_snapshot']['path']
        stand=paired[0]
        assert read(stand['actual_record']['path'])['kind']=='lean_standalone'
        assert read(paired[1]['actual_record']['path'])['kind']=='named_lean_module_build'
        out['proof_files'][source]={'sha256':sha(source),'selection_scope':'independently_whole_reviewed_module23_owned_new_source',
            'proof_selection_owner':'Modules23','standalone_compile_status':'passed',
            'standalone_compile_evidence':{'file':source,'sha256':sha(source),'exit_code':0,'source_unchanged':True,
                'log':stand['raw_log']['path'],'log_sha256':stand['raw_log']['sha256'],
                'compiler_manifest':stand['actual_record']['path'],'compiler_manifest_sha256':stand['actual_record']['sha256']},
            'actual_paired_records':paired,'declarations':names}
        new_paths.append(source);all_names+=names
        for name in names:
            match=re.search(r'^\s*(?:theorem|lemma)\s+'+re.escape(name.rsplit('.',1)[1])+r'\b',text,re.M);assert match,name
            out['declarations'].append({'name':name,'file':source,'line':text[:match.start()].count('\n')+1,
                                       'statement':text[match.start():].split(':=',1)[0].strip()})
        for module in re.findall(r'^import\s+(SafeLearning\.\S+)',text,re.M):
            name='verification/lean/'+module.replace('.','/')+'.lean'
            new_imports[name]=sha(name)
    # The new explicit scope supplement changes only node1012's declaration list.
    sref=inp['explicit_node1012_scope_supplement'];assert sha(sref['path'])==sref['sha256']
    supplement=read(sref['path']);assert supplement['original_review_entire_body_time_and_decisions_preserved'] is True
    u=supplement['material_units'][0];assert u['entire_inventory_record']==us['nn-in-the-loop.html::node-1012']
    target=ul[u['source_unit_key']+'::claim-review']
    assert set(target['lean_declarations']).issubset(u['lean_declarations']) and len(u['lean_declarations'])==len(target['lean_declarations'])+1
    for key,unitkey in [('hypotheses','hypotheses'),('correspondence','per_unit_reason')]:assert target[key]==u[unitkey]
    target['lean_declarations']=u['lean_declarations']
    target['explicit_dependency_scope_supplement']={'file':sref['path'],'sha256':sref['sha256'],
        'original_supplement_time':supplement['reviewed_at_utc'],'scope':'Only one earlier already-reviewed declaration is made explicit; original full review body/time/hypotheses/reason/status remain unchanged.'}
    assert sorted(mapped)==sorted(inp['whole_exercise_keys']) and len(mapped)==7
    assert set(mapped_units)==set(inp['material_unit_keys']) and len(mapped_units)==42
    assert len(new_paths)==4 and len(all_names)==len(set(all_names))==48
    pe={r['inventory_key']:r for r in old['exercises']};pu={r['id']:r for r in old['material_claims']}
    for row in out['exercises']:
        if row['inventory_key'] not in mapped:assert row==pe[row['inventory_key']]
    for row in out['material_claims']:
        if row['id'] not in {k+'::claim-review' for k in mapped_units}:assert row==pu[row['id']]
    assert {k:v for k,v in out['proof_files'].items() if k not in new_paths}==old['proof_files']
    assert out['declarations'][:len(old['declarations'])]==old['declarations']
    for n,h in new_imports.items():
        if n not in new_paths:out['required_external_import_dependencies'][n]=h
    out['generated_at_utc']=datetime.now(timezone.utc).isoformat()
    out['reviewed_work_integration23_candidate']={'input_bindings':{'file':INPUT,'sha256':sha(INPUT)},
        'baseline22_module_ledger':baseline,'fresh_whole_exercises':mapped,'fresh_material_units':sorted(mapped_units),
        'original_whole_reviews':review_refs,'original_material_review_decisions':43,
        'shared_instruction_unit':'nn-in-the-loop.html::node-998','new_source_files':new_paths,
        'required_safelearning_import_sha256':new_imports,'scope':'NEW isolated candidate only; no live22 ledger/source/offer or selection write.'}
    out['counts']={'exercises':len(out['exercises']),
        'exercise_status':dict(collections.Counter(e['status'] for e in out['exercises'])),
        'exercise_claim_status':dict(collections.Counter(c['status'] for e in out['exercises'] for c in e['claims'])),
        'material_claim_status':dict(collections.Counter(c['status'] for c in out['material_claims'])),
        'new_declarations':len(out['declarations'])}
    selection=read('reports/full-coverage/checkpoint-22-selection.json')
    assert selection['proof_file_count']==1113
    for n,r in selection['proof_files'].items():assert sha(n)==r['sha256']
    for n,h in inp['protected_owner_and_html_sha256'].items():assert sha(n)==h,n
    target=BASE+'/modules23-candidate-v1.json';put(target,out)
    guard=BASE+'/candidate-binding-integrity-v1.json'
    put(guard,{'status':'exact_seven_whole_forty_two_distinct_literal_candidate_bindings_and_held22_preservation_passed',
        'candidate_ledger':target,'candidate_ledger_sha256':sha(target),'input_bindings':{'file':INPUT,'sha256':sha(INPUT)},
        'baseline22_module_ledger':baseline,'fresh_whole_exercise_keys':mapped,'fresh_material_unit_keys':sorted(mapped_units),
        'original_whole_reviews':review_refs,'shared_nominal_instruction_unit_has_two_immutable_review_decisions':True,
        'counts':{'whole_exercises':7,'distinct_material_units':42,'original_material_review_decisions':43,
            'baseline_proof_rows_preserved':len(old['proof_files']),'baseline_exercise_bodies_preserved':len(old['exercises'])-7,
            'baseline_material_bodies_preserved':len(old['material_claims'])-42,'new_source_files':4,'public_theorem_exports':48,
            'actual_paired_records':8,'selected22_source_hashes_checked':1113},
        'required_safelearning_import_sha256':new_imports,'live_ledger_mutated':False,
        'scope':'Genuine isolated candidate construction and source/evidence checks. This is not a global ledger validation, live owner integration or fresh aggregate23 audit.'})
    print(json.dumps({'candidate':target,'candidate_sha256':sha(target),'guard':guard,'guard_sha256':sha(guard),'counts':out['counts']}))

if __name__=='__main__':build()
