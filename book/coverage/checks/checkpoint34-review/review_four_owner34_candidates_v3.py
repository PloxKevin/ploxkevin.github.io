#!/usr/bin/env python3
"""Independent minimal-delta, inverse, preserved-history and exact whole-route owner review."""
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import contextlib
import copy
import importlib.util
import json
import re
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
BASE=ROOT/'book/coverage/checks/checkpoint34-ledgers'
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations


def sha(path):
    import hashlib
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ref(path):
    return {'file':str(path.relative_to(ROOT)),'sha256':sha(path),'bytes':path.stat().st_size}


def exact(row):
    path=Path(row['file'])
    if not path.is_absolute():path=ROOT/path
    assert sha(path)==row['sha256'],row['file']
    if 'bytes' in row:assert path.stat().st_size==row['bytes']
    return path


def read(row):return json.loads(exact(row).read_bytes())
def encode(value):return (json.dumps(value,indent=2,ensure_ascii=False)+'\n').encode()


def access(document,path):
    for key in path:document=document[key]
    return document


def patch(document,patches,backward=False):
    for row in reversed(patches) if backward else patches:
        parent=access(document,row['pointer'][:-1]);key=row['pointer'][-1]
        old,new=('after','before') if backward else ('before','after')
        if row[old+'_exists']:assert parent[key]==row[old]
        elif isinstance(parent,list):assert key==len(parent)
        else:assert key not in parent
        if row[new+'_exists']:
            value=copy.deepcopy(row[new])
            if isinstance(parent,list) and key==len(parent):parent.append(value)
            else:parent[key]=value
        elif isinstance(parent,list):assert key==len(parent)-1;parent.pop()
        else:del parent[key]
    return document


def delta(a,b,path=()):
    if a==b:return {}
    rows={}
    if isinstance(a,dict) and isinstance(b,dict):
        for key in a.keys()|b.keys():
            current=path+(key,)
            if key not in a:rows[current]={'before_exists':False,'after_exists':True,'after':b[key]}
            elif key not in b:rows[current]={'before_exists':True,'before':a[key],'after_exists':False}
            else:rows.update(delta(a[key],b[key],current))
    elif isinstance(a,list) and isinstance(b,list) and len(b)>=len(a):
        for i,value in enumerate(a):rows.update(delta(value,b[i],path+(i,)))
        for i in range(len(a),len(b)):rows[path+(i,)]={'before_exists':False,'after_exists':True,'after':b[i]}
    else:rows[path]={'before_exists':True,'before':a,'after_exists':True,'after':b}
    return rows


def flatten(clauses,field):
    values=[value for clause in clauses for value in clause[field]]
    return sorted(set(values)) if field=='lean_declarations' else list(dict.fromkeys(values))


def main():
    started,tick=datetime.now(timezone.utc).isoformat(),time.monotonic()
    output=OUT/'independent-four-owner34-candidates-review-v3.json'
    assert not output.exists()
    binding_path=BASE/'owner-candidate-binding-v3.json'
    assert sha(binding_path)=='c85e6c3749bcb80601e0d61120d38638734540524a934e07e8f2bc30212740db'
    binding=json.loads(binding_path.read_bytes())
    inventory=read(binding['inventory']);baseline=read(binding['baseline_inventory'])
    qualification=read(binding['qualification_review']);impact=read(binding['component_rebase_review'])
    readiness=read(binding['canonical_readiness']);mapping=read(binding['exact_subclaims_and_assumptions'])
    assert qualification['errors']==impact['errors']==readiness['errors']==[]
    assert readiness['new_source_count']==3 and readiness['new_theorem_count']==114 and readiness['actual_compiler_command_count']==6
    material={row['key']:row for row in inventory['material_source_units']};exercises={row['key']:row for row in inventory['exercises']}
    mapped_material={row['key']:row for row in mapping['whole_material']}
    mapped_exercises={row['key']:row for row in mapping['whole_exercises']}
    assert len(mapped_material)==9 and set(mapped_exercises)=={'nn-in-the-loop.html::exercise-17','nn-in-the-loop.html::exercise-20'}
    for key,row in mapped_material.items():assert row['entire_current_literal']==material[key]
    for key,row in mapped_exercises.items():assert row['entire_current_literal']==exercises[key]
    selection_path=ROOT/'reports/full-coverage/checkpoint-33-selection.json'
    selection=json.loads(selection_path.read_bytes())
    allowed_sources={name:record['sha256'] for name,record in selection['proof_files'].items()}
    new_sources={row['canonical_source']['file']:row['canonical_source']['sha256'] for row in readiness['sources']}
    allowed_sources.update(new_sources)
    receipts=[]
    for row in readiness['sources']:
        source=exact(row['canonical_source']);packet=read(row['readiness'])
        assert source.read_bytes()==exact(packet['original_source']).read_bytes()
        for pair in row['actual_paired_records']:
            native=read(pair['actual_record']);assert native['actual_exit_code']==pair['actual_exit_code']==0
            assert exact(pair['source_snapshot']).read_bytes()==source.read_bytes();exact(pair['raw_log'])
            receipts.append(pair['actual_record'])
    assert len(mapping['used_declarations'])==94
    public_by_file={}
    for name,row in mapping['used_declarations'].items():
        source=exact(row['source']);filename=row['source']['file']
        assert allowed_sources[filename]==row['source']['sha256']
        if filename not in public_by_file:public_by_file[filename]={d['name'] for d in declarations(source.read_text())}
        assert name in public_by_file[filename]
    clauses=[clause for row in mapping['whole_material'] for clause in row['all_subclaim_correspondence']]
    clauses.extend(clause for row in mapping['whole_exercises'] for route in row['requirement_routes'].values() for clause in route)
    simulations=[c for c in clauses if c['classification']=='independently_reviewed_finite_observational_simulation']
    assert simulations and all(c['hypotheses']==['Exactly the extracted scalar tanh dynamics, initial states 1.9985 and 1.999, and 200 floating steps with 201 stored states.'] for c in simulations)
    for clause in clauses:
        assert clause['source_clause'] and clause['hypotheses']
        assert all(name in mapping['used_declarations'] for name in clause['lean_declarations'])
        assert clause['classification'] in {'independently_reviewed_actual_mathematical_subclaim','independently_reviewed_finite_observational_simulation'}
        if clause in simulations:assert clause['lean_declarations']==[];exact(clause['actual_evidence'])
    used_decl_names=set(mapping['used_declarations'])
    assert used_decl_names=={name for clause in clauses for name in clause['lean_declarations']}
    active={'source_text':'source_text','source_text_sha256':'text_sha256','text_sha256':'text_sha256','source_sha256':'source_sha256'}
    changed_top={'source_sha256','exercises','material_claims','proof_files','proof_sha256','counts','current_inventory','current_inventory_sha256'}
    decisions=[];candidates={};all_originals=[];promotions_total=0;requirements_total=0;preserved_proved_claims=0
    for replacement in binding['replacements']:
        before_path=exact(replacement['before']);candidate_path=exact(replacement['candidate']);inverse=read(replacement['exact_inverse'])
        before_raw,candidate_raw=before_path.read_bytes(),candidate_path.read_bytes()
        old,candidate=json.loads(before_raw),json.loads(candidate_raw);owner=before_path.stem
        assert encode(old)==before_raw and encode(candidate)==candidate_raw
        assert inverse['baseline']==replacement['before'] and inverse['candidate']==replacement['candidate']
        patch_map={tuple(p['pointer']):{k:v for k,v in p.items() if k!='pointer'} for p in inverse['patches']}
        assert len(patch_map)==len(inverse['patches']) and patch_map==delta(old,candidate)
        restored=patch(copy.deepcopy(candidate),inverse['patches'],True);assert encode(restored)==before_raw;del restored
        forward=patch(copy.deepcopy(old),inverse['patches']);assert encode(forward)==candidate_raw;del forward
        assert set(candidate)-set(old)=={'current_checkpoint34_identity'} and set(old)<=set(candidate)
        assert all(old[key]==candidate[key] for key in old if key not in changed_top)
        assert old['scope_pages']==candidate['scope_pages']
        assert candidate['source_sha256']=={**old['source_sha256'],**{page:inventory['source_sha256'][page] for page in old['scope_pages']}}
        assert len(old['material_claims'])==len(candidate['material_claims']) and len(old['exercises'])==len(candidate['exercises'])
        promotion_indices={row['index']:row for row in replacement['approved_whole_promotions']}
        for i,original in enumerate(old['material_claims']):
            final=candidate['material_claims'][i];assert final['id']==original['id']
            keys=final.get('source_unit_keys',[])
            if len(keys)==1:
                for field,source_field in active.items():
                    if field in final:assert final[field]==material[keys[0]][source_field],(owner,i,field)
            if i in promotion_indices:
                key=promotion_indices[i]['key'];routes=mapped_material[key]['all_subclaim_correspondence']
                assert original['status']=='pending' and final['status']=='proved'
                assert final['original_pending_record']==original and final['source_unit_keys']==[key]
                assert final['statement_in_prose']==material[key]['source_text'] and final['remaining_gaps']==[]
                assert final['all_subclaim_correspondence']==routes and final['lean_declarations']==flatten(routes,'lean_declarations')
                assert final['hypotheses']==flatten(routes,'hypotheses');exact(final['independent_whole_literal_peer'])
                assert final['actual_canonical_readiness']==binding['canonical_readiness']
                promotions_total+=1
            else:
                assert {k:v for k,v in original.items() if k not in active}=={k:v for k,v in final.items() if k not in active},(owner,i,original['id'])
        for i,original in enumerate(old['exercises']):
            final=candidate['exercises'][i];key=original['inventory_key']
            for field,source_field in active.items():
                if field in final:assert final[field]==exercises[key][source_field]
            if key not in mapped_exercises:
                assert {k:v for k,v in original.items() if k not in active}=={k:v for k,v in final.items() if k not in active}
                continue
            assert owner=='modules' and final['status']=='complete_math' and len(final['claims'])==len(original['claims'])
            requirement_routes=mapped_exercises[key]['requirement_routes']
            pending={str(j) for j,c in enumerate(original['claims']) if c['status']=='pending'}
            assert pending==set(requirement_routes)
            for j,c in enumerate(original['claims']):
                new=final['claims'][j]
                if str(j) not in requirement_routes:
                    assert new==c
                    if c['status']=='proved':preserved_proved_claims+=1
                    continue
                routes=requirement_routes[str(j)]
                assert new['original_pending_record']==c and new['remaining_gaps']==[]
                assert new['status']==('definition_encoded' if key.endswith('exercise-20') and j==0 else 'proved')
                expected=c['statement_in_prose']
                if key.endswith('exercise-17') and j==1:expected=expected.replace('find the largest interval certified with local sectors and check it by simulation.','find the supremal open interval obtained as the union of strict local-sector certificates, and check representative trajectories by simulation.')
                assert new['statement_in_prose']==expected
                assert new['all_subclaim_correspondence']==routes and new['lean_declarations']==flatten(routes,'lean_declarations')
                assert new['hypotheses']==flatten(routes,'hypotheses');exact(new['independent_whole_exercise_peer'])
                requirements_total+=1
            assert final['current_checkpoint34_whole_correspondence']['exact_literal']==exercises[key]
        additions={name:fingerprint for name,fingerprint in new_sources.items() if owner==('applied' if 'AppliedConditional' in name else 'modules')}
        old_files=old['proof_files']
        if isinstance(old_files,list):assert candidate['proof_files']==old_files+list(additions)
        else:assert candidate['proof_files']=={**old_files,**additions}
        if 'proof_sha256' in candidate:assert candidate['proof_sha256']=={**old.get('proof_sha256',{}),**additions}
        for key,value in old['counts'].items():
            if key in ('exercise_status','exercise_statuses'):assert candidate['counts'][key]==dict(Counter(e['status'] for e in candidate['exercises']))
            elif key in ('material_claim_status','material_claim_statuses'):assert candidate['counts'][key]==dict(Counter(c['status'] for c in candidate['material_claims']))
            elif key=='exercise_claim_status':assert candidate['counts'][key]==dict(Counter(c['status'] for e in candidate['exercises'] for c in e['claims']))
            else:assert candidate['counts'][key]==value
        identity=candidate['current_checkpoint34_identity'];assert identity['inventory']==binding['inventory']
        assert identity['old_checkpoint33_identity_and_all_historical_evidence_preserved'] and identity['owner_installation_and_selected_aggregate_kernel_axiom_audit_pending']
        decisions.append({'owner':owner,'before':replacement['before'],'candidate':replacement['candidate'],'exact_inverse':replacement['exact_inverse'],
                          'minimal_actual_changed_leaf_count':len(patch_map),'exact_forward_and_inverse_bytes_passed':True,
                          'whole_material_promotions':replacement['approved_whole_promotions'],'whole_exercises':replacement['approved_whole_exercises'],
                          'all_other_active_semantics_pending_statuses_and_historical_fields_preserved':True})
        candidates[owner]=candidate_path;all_originals.append(replacement['before'])
        del old,candidate,inverse,patch_map,before_raw,candidate_raw
    assert promotions_total==7 and requirements_total==9 and preserved_proved_claims==16
    narrow_path=OUT/'independent-IQC-existing-whole-and-exercise-carry-review-v2.json'
    narrow=json.loads(narrow_path.read_bytes());assert narrow['errors']==[]
    validator_path=ROOT/'book/coverage/validate.py'
    spec=importlib.util.spec_from_file_location('independent_owner34_validator',validator_path);validator=importlib.util.module_from_spec(spec);spec.loader.exec_module(validator)
    log=OUT/'independent-four-owner34-validator-v3.log'
    with tempfile.TemporaryDirectory(prefix='independent-owner34-current90-') as directory:
        tree=Path(directory);(tree/'book/coverage').mkdir(parents=True);(tree/'verification').mkdir()
        (tree/'SafeLearning').symlink_to(ROOT/'SafeLearning',target_is_directory=True)
        (tree/'verification/lean').symlink_to(ROOT/'verification/lean',target_is_directory=True)
        (tree/'book/coverage/inventory.json').symlink_to(exact(binding['inventory']))
        for owner,path in candidates.items():(tree/f'book/coverage/{owner}.json').symlink_to(path)
        validator.ROOT=tree
        with log.open('x') as stream,contextlib.redirect_stdout(stream),contextlib.redirect_stderr(stream):audit=validator.validate()
    assert audit['integrity_status']=='passed' and audit['errors']==[] and not audit['mathematical_coverage_complete']
    assert audit['counts']['material_review_statuses']=={'reviewed':4858,'pending':7916}
    assert {k:v for k,v in audit['counts']['statuses'].items() if k.startswith('exercise:')}=={'exercise:complete_math':538,'exercise:pending':11,'exercise:partial':7}
    audit_path=OUT/'independent-four-owner34-ledger-audit-v3.json';assert not audit_path.exists();audit_path.write_bytes(encode(audit))
    for row in all_originals:exact(row)
    for replacement in binding['replacements']:exact(replacement['candidate']);exact(replacement['exact_inverse'])
    for name,fingerprint in allowed_sources.items():assert sha(ROOT/name)==fingerprint
    execution_path=BASE/'isolated-validator-execution-v3.json';execution=json.loads(execution_path.read_bytes());assert execution['status']=='passed' and execution['actual_exit_code']==0
    report={'status':'approved_independent_four_Source90_owner34_v3_candidates_exact_inverse_seven_new_wholes_two_exercises_and_preserved_old_proofs',
        'errors':[],'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
        'binding':ref(binding_path),'exact_routes':binding['exact_subclaims_and_assumptions'],'builder':binding['builder'],'route_helper':binding['route_helper'],
        'all94_used_declarations_match_selected33_or_exact_three34_sources':True,'all_six_actual_canonical_readiness_native_records_checked':receipts,
        'owner_decisions':decisions,'new_whole_material_promotions':7,'whole_material_target_count_including_two_existing_wholes':9,
        'closed_exercises':['nn-in-the-loop.html::exercise-17','nn-in-the-loop.html::exercise-20'],'closed_existing_pending_requirements':9,
        'old_IQC_sixteen_proved_claims_preserved_exactly':16,'old_two_IQC_whole_material_rows_preserved':ref(narrow_path),
        'unchanged_literal_578_existing_proved_row_carry_authority':binding['component_rebase_review'],
        'finite_simulation_exact_initials':[1.9985,1.999],'finite_simulation_steps_and_states':[200,201],
        'finite_simulation_classification_kept_observational_with_zero_Lean_declarations':True,
        'fresh_independent_candidate_ledger_audit':ref(audit_path),'fresh_independent_validator_raw_log':ref(log),
        'builder_actual_validator':ref(execution_path),'material_counts':audit['counts']['material_review_statuses'],
        'exercise_counts':{k:v for k,v in audit['counts']['statuses'].items() if k.startswith('exercise:')},
        'preserved_read_only_inspector_schema_failure':ref(OUT/'owner34-read-only-route-inspection-schema-failure-v1.json'),
        'superseded_v1_failure_v2_mechanical_pass_and_incorrect_seed_description_retained':ref(BASE/'candidate-v1-v2-v3-supersession-comparison-v1.json'),
        'installation_aggregate_kernel_axiom_or_publication_performed_by_review':False,'coverage_complete':False}
    output.write_bytes(encode(report));print(json.dumps(ref(output)),flush=True)


if __name__=='__main__':main()
