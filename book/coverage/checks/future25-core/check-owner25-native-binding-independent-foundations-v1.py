"""Read-only independent actual owner25 binding-output checks; never main/dry/apply."""
from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/future25-core'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda n:{'file':n,'sha256':H(ROOT/n)}
def safe(n):
    assert isinstance(n,str)
    p=Path(n)
    assert not p.is_absolute() and '..' not in p.parts and str(p)==n
    q=ROOT/p
    assert q.resolve().is_relative_to(ROOT.resolve())
    return q
def read(n):return json.loads(safe(n).read_text())
def check(r):
    assert set(r)=={'file','sha256'} and re.fullmatch('[0-9a-f]{64}',r['sha256'])
    assert H(safe(r['file']))==r['sha256']
    return read(r['file'])
def alias(d,keys):
    v=[d[k] for k in keys if k in d]
    assert v and all(x==v[0] for x in v)
    return v[0]
def zero(d):
    v=[d[k]for k in ['actual_exit_code','exit_code']if k in d]
    assert v and all(type(x)is int and x==0 for x in v)
def pointer(d,p):
    for k in p:d=d[k]
    return d
BINDING='book/coverage/checks/root-owner25-reviewed-candidate-bindings-v1.json'
INPUT='book/coverage/checks/root-owner25-binding-preparation-inputs-v1.json'
HELPER='book/coverage/checks/prepare_root_owner25_bindings_v2.py'
assert H(ROOT/HELPER)=='71f19be2c4a8f3a61966810e1453e90b3008243963c6e3164952b507a3ac9c9a'
assert H(ROOT/INPUT)=='9f4f860c9267f7973840f870d72bfae146d4a1e7757e8a4c9fd92c6b303b929d'
config=read(INPUT)
binding=read(BINDING)
assert binding['preparation_input']==ref(INPUT) and binding['preparation_helper']==ref(HELPER)
actual_name='reports/full-coverage/prepare-owner25-bindings-execution-v1.json'
actual=read(actual_name)
zero(actual)
assert actual['status']=='passed'
assert actual['actual_command']==['python3',HELPER,'--input',INPUT,'--input-sha256',H(ROOT/INPUT),'--root-authorized-binding-preparation']
assert actual['actual_workdir']==str(ROOT)
assert actual['helper_sha256_before']==actual['helper_sha256_after']=={HELPER:H(ROOT/HELPER)}
assert H(ROOT/actual['log'])==actual['log_sha256']
assert actual['started_at_utc']<=binding['prepared_at_utc']<=actual['finished_at_utc']
# Reconstruct against the real request by calling only the pure read-only function.
# No main, production writer or synthetic missing peer is executed.
t=ast.parse((ROOT/HELPER).read_text())
ns={'__file__':str(ROOT/HELPER),'__name__':'independent_read_only_output_review'}
nodes=[n for n in t.body if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef,ast.Assign))]
exec(compile(ast.Module(body=nodes,type_ignores=[]),HELPER,'exec'),ns)
reconstructed=ns['build_binding'](config,INPUT)
reconstructed['prepared_at_utc']=binding['prepared_at_utc']
assert reconstructed==binding
assert binding['status']=='all_four_reviewed_current52_owner_candidates_bound_ready_for_root_execution'
assert binding['coverage_complete']is False and set(binding['owners'])=={'core','foundations','applied','modules'}
manifest=check(binding['baseline24_manifest'])
assert len(manifest['proof_files'])==1144
assert H(ROOT/'book/coverage/inventory.json')==binding['inventory_sha256']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assets=binding['exact_current52_safelearning_assets_sha256']
assert len(assets)==31
assert assets=={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')}
for n,h in assets.items():assert H(ROOT/n)==h
held={n:manifest['working_inputs_sha256'][n]for n in ['book/coverage/'+o+'.json'for o in binding['owners']]+['book/coverage/applied-promotions.json']}
for n,h in held.items():assert H(ROOT/n)==h
for n,r in manifest['proof_files'].items():assert H(ROOT/n)==r['sha256']
seen={}
pair_observations=[]
semantic_bodies={}
owner_observations={}
for owner,row in binding['owners'].items():
    assert row['ready']is True and row['held24_ledger']=='book/coverage/'+owner+'.json'
    assert row['held24_ledger_sha256']==held[row['held24_ledger']]
    assert row['reviewed_final_offer']==config['offers'][owner]
    offer=check(row['reviewed_final_offer'])
    candidate=check(row['candidate_ledger'])
    peer=check(row['independent_candidate_mapping_peer'])
    assert 'passed' in peer['status'] and peer.get('errors',[])==[]
    assert pointer(offer,row['offer_candidate_path_pointer'])==row['candidate_ledger']['file']
    assert pointer(offer,row['offer_candidate_sha256_pointer'])==row['candidate_ledger']['sha256']
    assert pointer(peer,row['peer_candidate_path_pointer'])==row['candidate_ledger']['file']
    assert pointer(peer,row['peer_candidate_sha256_pointer'])==row['candidate_ledger']['sha256']
    build=check(row['actual_candidate_builder'])
    zero(build)
    assert H(ROOT/alias(build,('log','raw_log')))==alias(build,('log_sha256','raw_log_sha256'))
    for s in row['original_full_source_semantic_reviews']:
        original=check({k:s[k]for k in ['file','sha256']})
        assert original['status']==s['original_review_status'] and original.get('errors',[])==[]
        assert original.get('reviewed_at_utc',original.get('checked_at_utc'))==s['original_review_time']
        semantic_bodies[s['file']]=original
    evidence={}
    for e in row['additional_exact_provenance']:
        assert H(safe(e['file']))==e['sha256']
        assert e['file']not in evidence or evidence[e['file']]==e['sha256']
        evidence[e['file']]=e['sha256']
    assert len(row['new_immutable_proof_sources'])=={'core':1,'foundations':2,'applied':7,'modules':2}[owner]
    for source,p in row['new_immutable_proof_sources'].items():
        assert source not in seen and source not in manifest['proof_files']
        assert H(ROOT/source)==p['sha256']
        seen[source]=p['sha256']
        assert offer['proof_files'][source]['sha256']==p['sha256']
        expected=[['lake','env','lean',str(Path(source).relative_to('verification/lean'))],['lake','build','SafeLearning.'+Path(source).stem]]
        assert len(p['actual_pair'])==2
        for normalized,command in zip(p['actual_pair'],expected):
            record=check({k:normalized[k]for k in ['file','sha256']})
            zero(record)
            assert alias(record,('command','actual_command'))==command==normalized['actual_command']
            assert normalized['actual_source']==source and record['source']==source
            assert record['source_sha256_before']==record['source_sha256_after']==p['sha256']
            assert record.get('source_unchanged',True)is True
            assert normalized['actual_workdir']==record['actual_workdir']==str(ROOT/'verification/lean')
            log=normalized['canonical_raw_log']
            assert log['sha256']==alias(record,('log_sha256','raw_log_sha256'))
            assert H(safe(log['file']))==log['sha256'] and evidence[log['file']]==log['sha256']
            assert normalized['file']in evidence and evidence[normalized['file']]==normalized['sha256']
            for field in ['source_snapshot_sha256','preserved_source_sha256']:
                if field in record:
                    assert record[field]==p['sha256'] and any(n.endswith('.lean')and h==p['sha256']for n,h in evidence.items())
            pair_observations.append({'owner':owner,'source':source,'source_sha256':p['sha256'],'original_native_record':{k:normalized[k]for k in ['file','sha256']},'original_entire_record_and_time':record,'canonical_raw_log':log})
    assert len(row['companion_candidates'])==(1 if owner=='applied'else 0)
    for companion in row['companion_candidates']:
        assert companion['held24_asset']=='book/coverage/applied-promotions.json' and companion['held24_asset_sha256']==held[companion['held24_asset']]
        check(companion['candidate'])
        assert companion['candidate']=={'file':offer['mapped_promotions'],'sha256':offer['mapped_promotions_sha256']}
    owner_observations[owner]={'original_final_offer':row['reviewed_final_offer'],'candidate':row['candidate_ledger'],'mapping_peer':row['independent_candidate_mapping_peer'],'semantic_originals':row['original_full_source_semantic_reviews'],'actual_candidate_builder':row['actual_candidate_builder'],'new_source_count':len(row['new_immutable_proof_sources']),'closed_provenance_count':len(evidence)}
assert len(seen)==binding['new_proof_sources']==12 and len(pair_observations)==binding['original_canonical_execution_records']==24
catalog_ref=config['actual_completed24_delivery_originals']
catalog=check(catalog_ref)
assert catalog_ref['sha256']=='bb5037892e16c06ae7ee8f7e43f98e675531004d70c0bd1c3d72beb9de716959'
assert catalog['both_actual_pages_runs_and_all31_live_assets_passed']is True and len(catalog['aliases'])==161
core_evidence={x['file']:x['sha256']for x in binding['owners']['core']['additional_exact_provenance']}
assert core_evidence[catalog_ref['file']]==catalog_ref['sha256']
for a in catalog['aliases']:
    orig=a['original']
    copy_ref=a['immutable_original_byte_copy']
    assert orig['sha256']==copy_ref['sha256'] and H(safe(copy_ref['file']))==copy_ref['sha256']
    assert core_evidence[copy_ref['file']]==copy_ref['sha256']
absolute=catalog['original_absolute_recorder_byte_alias']
assert H(safe(absolute['canonical_file']))==absolute['sha256']==H(Path(absolute['original_absolute_path']))
assert core_evidence[absolute['canonical_file']]==absolute['sha256']
for n,h in held.items():assert H(ROOT/n)==h
report={'status':'independent_actual_four_owner25_native_binding_output_confirmation_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; binding author Modules','binding_manifest':ref(BINDING),'preparation_input':ref(INPUT),'actual_binding_preparation':ref(actual_name),'actual_binding_preparation_raw_log':ref(actual['log']),'helper_sha256':H(ROOT/HELPER),'entire_native_preparation_reconstructed_equal_except_generated_timestamp':True,'owners':owner_observations,'original_full_semantic_bodies_and_times':semantic_bodies,'twelve_sources_and_twenty_four_original_native_pairs':pair_observations,'all_161_completed24_delivery_canonical_original_aliases_exact':catalog_ref,'all1144_selected24_source_hashes_exact':True,'all31_current52_assets_exact':assets,'all_five_held24_live_owner_hashes_exact':held,'coverage_complete':False,'scope':'Fresh actual binding-output review only. All source/compiler/builder/semantic history is original; no mathematical redecision, compiler rerun, owner installation, global/selection/freeze/audit25 or publication claim. The pure preparation function was called read-only against the genuine closed request, never main/dry/apply.'}
out=BASE/'owner25-native-binding-independent-foundations-observations-v1.json'
assert not out.exists()
out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':report['status'],'binding_manifest':ref(BINDING),'observation':ref(str(out.relative_to(ROOT))),'sources':12,'actual_pairs':24,'owners':4,'delivery_original_aliases':161}))
