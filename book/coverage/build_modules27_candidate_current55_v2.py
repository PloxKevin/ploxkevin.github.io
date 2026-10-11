"""Build an isolated current55 Module27 candidate from actual canonical pairs.

Keeps installed26 owners and selected1167 sources unchanged. The entire source55
mapping draft and original review times are preserved; only genuine canonical
proof metadata and active byte-alias pointers are finalized. No live installation.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,collections,copy,hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/modules-future27/source55'
READY='book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json'
DRAFT='/tmp/modules27-current55-two-whole-mapping-draft-v1/modules27-current55-two-whole-mapping-draft-v1.json'
DRAFT_SHA='1926ee49a419d5c9ef97f9859767b7481652eb24f3a7f022f83c4d3a9a93455c'
PEER='/tmp/modules27-current55-two-whole-draft-independent-foundations-mechanics-review-v1.json'
PEER_SHA='5d140ce68b84264b92390420f3ad25186d6158d91f3393935d97dec32c16a5ab'
HELPER2='book/coverage/checks/run_root27_eight_source141_canonical_pairs_v2.py'
HELPER2_SHA='30dda287631fe698f4d39ef16a5c92b42cee332dfcf7bc45a178630d1f4de8c0'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def locate(n):
    p=Path(n)
    if not p.is_absolute():
        assert p.as_posix()==n and '..' not in p.parts
        p=ROOT/p
    assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to(Path('/tmp'))
    assert p.is_file() and not p.is_symlink(),str(p)
    return p
def checked(ref):
    assert set(ref)=={'file','sha256'} and re.fullmatch('[0-9a-f]{64}',ref['sha256'])
    p=locate(ref['file']);assert sha(p)==ref['sha256'],str(p);return p
def ref(n):return {'file':str(n),'sha256':sha(locate(str(n)))}
def protection():
    PINNED = {
        'reports/full-coverage/checkpoint-26-selection.json': '12527ed93a283e1b37a491f7f799ac04e6217b1d7e20aee74116b312e580e23f',
        'reports/full-coverage/checkpoint-25-selection.json': '3559445215b6b5b9bd176363ded8d307a93724b2b68c1ba9845dc709a3b4ddff',
        'reports/full-coverage/checkpoint-25-manifest.json': '0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363',
        'book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json': '00a94eefea80aff4bd57ee2d511d3102f1a8652dfda1977272aefd9b7fe41cfb',
        'reports/full-coverage/owner26-reviewed-candidate-integration-v1.json': '7fa88d829c47797ab8258eb84ff5c7ce3399da66c9b03b591ea9820ca1eca06e',
        'reports/full-coverage/root-source53-final-owner-integration26-v1.json': '4029138dca32a74e8fd718fbe563d0b867d8ed408ad49a869e7308ea9867259d',
        'book/coverage/inventory.json': '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf',
        'book/coverage/inventory-after-correction55.json': '82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf',
        'reports/full-coverage/source54-55-corrections-application-v1.json': '845937be3efd0d3bb88518fe9597b4bf6f22ead237cd1292a28ad5b16265c528',
        'reports/full-coverage/source54-55-corrections-application-execution-v1.json': 'a255862de464e0f1acf284807c4a48b732bc69055cf71b445ea2df5920494805',
        'book/coverage/material-corrections.json': '21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94',
        'book/coverage/inventory-after-correction53.json': '4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be',
    }
    for name, digest in PINNED.items(): assert sha(ROOT / name) == digest, name
    selection = read('reports/full-coverage/checkpoint-26-selection.json')
    baseline = read('reports/full-coverage/checkpoint-25-selection.json')
    binding = read('book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json')
    integration = read('reports/full-coverage/owner26-reviewed-candidate-integration-v1.json')
    global_audit = read('reports/full-coverage/root-source53-final-owner-integration26-v1.json')
    assert selection['proof_file_count'] == len(selection['proof_files']) == 1167
    assert selection['new_file_count'] == binding['new_proof_sources'] == 11
    assert len(baseline['proof_files']) == 1156
    assert set(baseline['proof_files']) <= set(selection['proof_files'])
    assert all(selection['proof_files'][n]['sha256'] == r['sha256'] for n, r in baseline['proof_files'].items())
    assert global_audit['integrity_status'] == 'passed' and global_audit['errors'] == []
    assert integration['applied'] is True and integration['all44111_frozen25_inputs_exact'] is True
    assert integration['all1156_selected25_root_source_hashes_exact'] is True
    application = read('reports/full-coverage/source54-55-corrections-application-v1.json')
    assert application['status'] == 'passed_actual_source54_and_source55_corrections_full29_inventory_owner_identity_rebase_pending'
    assert application['selected26_proof_sources_unchanged'] == 1167
    assert application['five_installed26_owner_ledgers_unchanged'] is True
    assert application['coverage_complete'] is False
    assert [r['correction_id'] for r in application['applications']] == [54,55]
    expected_changed_assets = {
        'SafeLearning/lyapunov-mpc.html': '63a1ac8be7f5cf8b490dd1dd872d416affee95f6de0d5ba3c1c618f4b86cd79f',
        'SafeLearning/verification.html': 'd01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53',
    }
    assert {r['source_after']['file']:r['source_after']['sha256'] for r in application['applications']} == expected_changed_assets
    assets = {**binding['exact_current53_safelearning_assets_sha256'],**expected_changed_assets}
    assert len(assets) == 31
    assert read('book/coverage/inventory-after-correction55.json')['source_sha256'] == {n:h for n,h in assets.items() if n.endswith('.html')}
    owners = {r['destination']: r['candidate']['sha256'] for r in integration['exact_replacements']}
    assert len(owners) == 5
    for row in global_audit['domains']:
        assert row['ledger_sha256'] == owners['book/coverage/' + row['domain'] + '.json']
    held = {n: r['sha256'] for n, r in selection['proof_files'].items()}
    held.update(assets)
    held.update(owners)
    corrections = 'book/coverage/material-corrections.json'
    assert len(read(corrections)['corrections']) == 55
    old_corrections_path = ROOT / 'reports/full-coverage/source-history/approved-mpc-conformal-corrections54-55-20261011/source53-original-root/book/coverage/material-corrections.json'
    assert sha(old_corrections_path) == binding['source53_corrections_sha256']
    assert read(corrections)['corrections'][:53] == json.loads(old_corrections_path.read_text())['corrections']
    assert [r['correction_id'] for r in read(corrections)['corrections'][53:]] == [54,55]
    for stem in ('owner26-integration-apply-execution-v1', 'root-source53-final-owner-integration26-execution-v1', 'prepare-checkpoint26-selection-execution-v1', 'source54-55-corrections-application-execution-v1'):
        name = 'reports/full-coverage/' + stem + '.json'
        actual = read(name)
        codes = [actual[k] for k in ('actual_exit_code', 'exit_code') if k in actual]
        assert codes and all(type(code) is int and code == 0 for code in codes)
        assert actual['actual_workdir'] == str(ROOT)
        assert actual['helper_sha256_before'] == actual['helper_sha256_after']
        assert sha(ROOT / actual['log']) == actual['log_sha256']
        for helper, digest in actual['helper_sha256_after'].items():
            assert sha(ROOT / helper) == digest
            PINNED[helper] = digest
        PINNED[name] = sha(ROOT / name)
        PINNED[actual['log']] = actual['log_sha256']
    for name in ('verification/lean/lean-toolchain', 'verification/lean/lakefile.toml', 'verification/lean/lake-manifest.json'):
        PINNED[name] = sha(ROOT / name)

    return {**held,**PINNED}
def guard(protected,before):
    for n,h in protected.items():assert sha(ROOT/n)==h,n
    assert sha(Path(__file__))==before

def main(pair_execution):
    protected=protection();before=sha(Path(__file__));guard(protected,before)
    assert not BASE.exists()
    assert sha(ROOT/HELPER2)==HELPER2_SHA and sha(locate(DRAFT))==DRAFT_SHA and sha(locate(PEER))==PEER_SHA
    assert sha(ROOT/READY)=='74f6e5413cb390698e6090b798d6f0eed0b667082bd24681f7b2e82c49deef1f'
    ready=read(READY);assert ready['errors']==[] and ready['source_count']==8 and ready['public_theorem_count']==141 and ready['actual_compiler_command_count']==16
    for row in ready['sources']:
        n=row['canonical_source'];h=row['source']['sha256'];assert sha(ROOT/n)==h;protected[n]=h
    protected[READY]=sha(ROOT/READY)
    assert ready['actual_helper']=={'file':str(ROOT/HELPER2),'sha256':HELPER2_SHA}
    assert pair_execution=='reports/full-coverage/eight-source141-canonical-pairs27-execution-v1.json' and sha(ROOT/pair_execution)=='9ee7428bc5d16d6b65ec0fd88877d85e3ba38cb879f11951eca72ddd0b6df384'
    execution=read(pair_execution);codes=[execution[k] for k in ('actual_exit_code','exit_code') if k in execution]
    assert codes and all(type(c) is int and c==0 for c in codes)
    assert execution['actual_workdir']==str(ROOT)
    assert execution['helper_sha256_before']==execution['helper_sha256_after']
    assert execution['helper_sha256_after'][HELPER2]==HELPER2_SHA
    actual_command=execution['actual_command'];assert actual_command[1:]==[HELPER2,'--apply']
    logname=execution.get('log',execution.get('raw_log'));logsha=execution.get('log_sha256',execution.get('raw_log_sha256'))
    checked({'file':logname,'sha256':logsha})
    draft=json.loads(locate(DRAFT).read_text());peer=json.loads(locate(PEER).read_text())
    assert peer['errors']==[] and 'passed' in peer['status']
    assert peer['candidate']=={'file':DRAFT,'sha256':DRAFT_SHA}
    old=read('book/coverage/modules.json');assert sha(ROOT/'book/coverage/modules.json')=='c1e25f304082945e44212cdc5f1943108caf9b5052d0b3afae586e8700492231'
    plans=draft['reviewed_current55_two_whole_mapping_draft27']['planned_four_new_sources'];assert len(plans)==4 and sum(p['public_theorem_count'] for p in plans)==87
    own={p['canonical_source'] for p in plans};assert own==set(draft['proof_files'])-set(old['proof_files'])
    aliases=copy.deepcopy(ready['original_closed_byte_aliases']);evidence={READY:sha(ROOT/READY),HELPER2:HELPER2_SHA,pair_execution:sha(ROOT/pair_execution),logname:logsha}
    for k,item in aliases.items():
        assert k==item['original_file']+'::'+item['original_sha256'] and item['original_sha256']==item['sha256']
        checked({'file':item['file'],'sha256':item['sha256']});evidence[item['file']]=item['sha256']
    pairs={n:[] for n in own}
    for p in ready['actual_paired_records']:
        if p['source']['file'] not in own:continue
        n=p['source']['file'];h=draft['proof_files'][n]['sha256'];assert p['source']['sha256']==h==sha(ROOT/n)
        assert type(p['actual_exit_code']) is int and p['actual_exit_code']==0
        record=json.loads(checked(p['actual_record']).read_text());assert type(record['exit_code']) is int and record['exit_code']==0
        assert record['source']==n and record['source_sha256_before']==record['source_sha256_after']==h and record['source_unchanged'] is True
        assert record['actual_workdir']==str(ROOT/'verification/lean')
        name=Path(n).stem;expected=['lake','env','lean','SafeLearning/'+name+'.lean'] if p['kind']=='standalone' else ['lake','build','SafeLearning.'+name]
        assert p['kind'] in {'standalone','named'} and record['command']==expected
        assert p['raw_log']=={'file':record['log'],'sha256':record['log_sha256']} and p['source_snapshot']['sha256']==h
        for k in ('actual_record','raw_log','source_snapshot'):checked(p[k]);evidence[p[k]['file']]=p[k]['sha256']
        evidence[n]=h;pairs[n].append(copy.deepcopy(p))
    assert sum(len(v) for v in pairs.values())==8
    for n,v in pairs.items():assert len(v)==2 and {p['kind'] for p in v}=={'standalone','named'}
    # New reviewer/preparer bytes were closed after the combined executor input
    # was fixed; preserve them explicitly, without changing its original packet.
    local={DRAFT:DRAFT_SHA,PEER:PEER_SHA,str(Path(__file__)):before,pair_execution:sha(ROOT/pair_execution),logname:logsha,'book/coverage/build_modules27_candidate_current55_v1.py':sha(ROOT/'book/coverage/build_modules27_candidate_current55_v1.py')}
    local.update(peer['closed_evidence_sha256'])
    for n,h in local.items():checked({'file':n,'sha256':h})
    for n in ['/tmp/prepare-modules27-current55-two-whole-mapping-draft-v1.py','/tmp/modules27-current55-two-whole-mapping-draft-v1/modules27-current55-owned-literal-identity-and-mapping-inputs-v1.json','/tmp/modules27-current55-two-whole-mapping-draft-v1/modules27-current55-four-source-canonical-pair-planning-request-v1.json']:
        local[n]=sha(locate(n))
    def active_alias(v):
        k=v['file']+'::'+v['sha256'];assert k in aliases
        a=aliases[k];return {'file':a['file'],'sha256':a['sha256']}
    # Validate every active mathematical peer can be resolved before any output.
    for p in plans:active_alias(p['whole_peer'])
    candidate=copy.deepcopy(draft);changes={'original_generated_at_utc':draft['generated_at_utc'],'original_new_proof_rows':{n:copy.deepcopy(draft['proof_files'][n]) for n in own},'original_declaration_suffix':copy.deepcopy(draft['declarations'][len(old['declarations']):]),'active_reference_replacements':[]}
    for n in own:
        row=candidate['proof_files'][n];row.update(proof_selection_owner='Modules27 isolated candidate, unselected',standalone_compile_status='passed_source_matched_actual_canonical_standalone_and_named',actual_paired_records=pairs[n],canonical_pair_execution_claimed=True)
        row['evidence_sha256']=copy.deepcopy(evidence)
        p=next(p for p in plans if p['canonical_source']==n);row['independent_full_source_review']=active_alias(p['whole_peer'])
    for decl in candidate['declarations'][len(old['declarations']):]:assert decl.pop('canonical_source_execution_pending') is True
    exkeys=set(draft['reviewed_current55_two_whole_mapping_draft27']['fresh_whole_exercise_keys']);unitids={k+'::claim-review' for k in draft['reviewed_current55_two_whole_mapping_draft27']['fresh_whole_material_unit_keys']}
    for e in candidate['exercises']:
        if e['inventory_key'] not in exkeys:continue
        fields=[('independent_current55_full_source_review27',e)]
        fields.extend(('independent_source_review',c) for c in e['claims'])
        for field,obj in fields:
            orig=copy.deepcopy(obj[field]);obj[field]=active_alias(orig);changes['active_reference_replacements'].append({'kind':'exercise' if obj is e else 'exercise_claim','key':e['inventory_key'] if obj is e else obj['id'],'field':field,'original':orig,'canonical_alias':obj[field]})
    for c in candidate['material_claims']:
        if c['id'] not in unitids:continue
        orig=copy.deepcopy(c['independent_source_review']);c['independent_source_review']=active_alias(orig);changes['active_reference_replacements'].append({'kind':'material_claim','key':c['id'],'field':'independent_source_review','original':orig,'canonical_alias':c['independent_source_review']})
    candidate['generated_at_utc']=datetime.now(timezone.utc).isoformat()
    # Entire original pending-draft metadata remains historical and byte-exact.
    candidate['reviewed_work_integration27_candidate']={'status':'isolated_current55_canonical_pairs_ready_final_independent_candidate_mechanics_pending','original_reviewed_mapping_draft':{'file':DRAFT,'sha256':DRAFT_SHA},'original_independent_draft_mechanics':{'file':PEER,'sha256':PEER_SHA},'actual_combined_canonical_readiness':ref(READY),'actual_combined_canonical_execution':ref(pair_execution),'strict_reversible_finalization_changes':changes,'whole_exercise_count':2,'whole_material_unit_count':8,'new_source_count':4,'new_public_export_count':87,'genuine_canonical_execution_records':8,'installed_owner_mutation':False,'whole_corpus_coverage_complete':False}
    # Reverse only proof metadata/active aliases/time to recover the exact
    # independently approved pending-pair draft. Its original inverse restores26.
    inverse=copy.deepcopy(candidate);inverse.pop('reviewed_work_integration27_candidate');inverse['generated_at_utc']=changes['original_generated_at_utc']
    inverse['proof_files'].update(changes['original_new_proof_rows']);inverse['declarations'][len(old['declarations']):]=changes['original_declaration_suffix']
    for a in changes['active_reference_replacements']:
        if a['kind']=='exercise':obj=next(e for e in inverse['exercises'] if e['inventory_key']==a['key'])
        elif a['kind']=='exercise_claim':obj=next(c for e in inverse['exercises'] for c in e['claims'] if c['id']==a['key'])
        else:obj=next(c for c in inverse['material_claims'] if c['id']==a['key'])
        assert obj[a['field']]==a['canonical_alias'];obj[a['field']]=a['original']
    assert inverse==draft
    assert candidate['proof_files'].keys()==draft['proof_files'].keys() and len(candidate['declarations'])==3259
    for n,r in old['proof_files'].items():assert candidate['proof_files'][n]==r
    guard(protected,before)
    # All guards, input hashes and mathematical inverses passed prewrite.
    BASE.mkdir(parents=True)
    for n,h in sorted(local.items()):
        p=locate(n);dest=BASE/'original-closed-bytes'/h/p.name;dest.parent.mkdir(parents=True,exist_ok=True)
        if dest.exists():assert sha(dest)==h
        else:
            with dest.open('xb') as f:f.write(p.read_bytes())
        key=n+'::'+h;aliases[key]={'original_file':n,'original_sha256':h,'file':dest.relative_to(ROOT).as_posix(),'sha256':h};evidence[dest.relative_to(ROOT).as_posix()]=h
    evidence.pop(pair_execution);evidence.pop(logname)
    executionalias=active_alias({'file':pair_execution,'sha256':sha(ROOT/pair_execution)})
    draftalias=active_alias({'file':DRAFT,'sha256':DRAFT_SHA});peeralias=active_alias({'file':PEER,'sha256':PEER_SHA})
    metadata=candidate['reviewed_work_integration27_candidate'];metadata['original_reviewed_mapping_draft']=draftalias;metadata['original_independent_draft_mechanics']=peeralias;metadata['actual_combined_canonical_execution']=executionalias
    # These two new metadata refs are canonical aliases; active math bodies remain
    # those checked in the exact inverse above.
    for n in own:candidate['proof_files'][n]['evidence_sha256']=copy.deepcopy(evidence)
    def put(name,body):
        p=BASE/name;assert not p.exists()
        with p.open('x') as f:f.write(json.dumps(body,indent=2,ensure_ascii=False)+'\n')
        return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
    cand=put('modules27-current55-two-whole-canonical-candidate-v1.json',candidate)
    interface=put('modules27-current55-two-whole-canonical-candidate-interface-v1.json',{'status':'prepared_actual_isolated_candidate_final_peer_pending','errors':[],'candidate_ledger':cand,'original_mapping_draft':draftalias,'original_independent_draft_peer':peeralias,'entire_original_mapping_peer_body_and_time':peer,'proof_source_count':4,'public_export_count':87,'whole_exercises':2,'whole_material_units':8,'exact_candidate_to_draft_inverse_checked':True,'all491_old_proof_rows_and3172_declaration_prefix_exact':True,'original_closed_byte_aliases':aliases,'actual_pairs':{n:pairs[n] for n in sorted(own)},'current55_inventory':ref('book/coverage/inventory.json'),'scope':'Actual paired evidence binds the already-approved current55 mapping. Fresh independent final candidate mechanics is required; installed26 owners unchanged.'})
    evidence[cand['file']]=cand['sha256'];evidence[interface['file']]=interface['sha256']
    offer={'status':'actual_isolated_current55_modules27_candidate_additions_final_mechanics_pending','errors':[],'inventory':'book/coverage/inventory.json','inventory_sha256':protected['book/coverage/inventory.json'],'mapped_ledger':cand['file'],'mapped_ledger_sha256':cand['sha256'],'candidate_ledger':cand,'candidate':cand,'candidate_builder':{'file':Path(__file__).resolve().relative_to(ROOT).as_posix(), 'sha256':before},'candidate_interface':interface,'proof_files':{n:candidate['proof_files'][n] for n in sorted(own)},'source_sha256':candidate['source_sha256'],'original_pending_pair_mapping_draft':draftalias,'original_independent_mapping_draft_peer':peeralias,'original_full_source_reviews':[active_alias(p['whole_peer']) for p in plans[:1]+plans[-1:]],'entire_original_conformal_full_review_body_and_time':draft['reviewed_current55_two_whole_mapping_draft27']['entire_original_conformal_whole_review_body_and_time'],'entire_original_viability_full_review_body_and_time':draft['reviewed_current55_two_whole_mapping_draft27']['entire_original_viability_whole_review_body_and_time'],'actual_combined_canonical_readiness':ref(READY),'actual_combined_canonical_execution':executionalias,'actual_paired_records':[p for n in sorted(own) for p in pairs[n]],'counts':{'new_sources':4,'new_public_exports':87,'whole_exercises':2,'whole_material_units':8},'required_evidence_artifacts_sha256':evidence,'additional_frozen_inputs':copy.deepcopy(evidence),'original_closed_byte_aliases':aliases,'final_independent_candidate_mapping_peer':None,'actual_isolated_candidate_preparation':None,'coverage_complete':False,'scope':'Module owns verification17/five units and viability16/three units. Three conformal sources supplied by Modules; Applied-supplied42 is selected solely by Modules. Original math/review/status/time retained. Isolated candidate only; final independent mechanics and actual Root guarded integration/global/selection/audit remain required.'}
    offerref=put('modules-audit27-candidate-current55-additions-draft-v1.json',offer)
    guard(protected,before)
    print(json.dumps({'status':'actual_isolated_candidate_prepared_final_mechanics_pending','candidate':cand,'interface':interface,'offer':offerref,'sources':4,'exports':87,'whole_exercises':2,'whole_units':8}))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--pair-execution',required=True);a=parser.parse_args();assert Path(a.pair_execution).parent==Path('reports/full-coverage');main(a.pair_execution)
