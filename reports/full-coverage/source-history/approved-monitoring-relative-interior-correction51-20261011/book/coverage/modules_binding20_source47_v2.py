"""Validate unchanged source44 decisions and independently reviewed source47 additions."""
from pathlib import Path
import hashlib,json,copy

def check_bindings(root,ledger,old,side,mapping):
    direct=lambda n:root/n
    digest=lambda n:hashlib.sha256(direct(n).read_bytes()).hexdigest()
    read=lambda n:json.loads(direct(n).read_text())
    aliases=read(mapping['canonical_path_aliases']['file'])['aliases']
    def resolve(n):
        name=aliases.get(n,{}).get('path',n)
        path=Path(name)
        assert not path.is_absolute() and '..' not in path.parts and str(path)==name,n
        return root/path
    sha=lambda n:hashlib.sha256(resolve(n).read_bytes()).hexdigest()
    raw=lambda n:json.loads(resolve(n).read_text())
    assert digest('book/coverage/inventory.json')==side['current_inventory']['sha256']==mapping['inventory_sha256']
    inv=read(side['current_inventory']['file']);historical=read(side['historical_inventory']['file'])
    assert digest(side['historical_inventory']['file'])==side['historical_inventory']['sha256']
    for section in ('exercises','material_source_units'):
        a={x['key']:x for x in historical[section] if x['source'] in old['scope_pages']}
        b={x['key']:x for x in inv[section] if x['source'] in old['scope_pages']}
        assert a==b and {x['key'] for x in side['unchanged_owned_literals'][section]}==set(a)
        assert not side['changed_owned_literals_excluded'][section]
    for row in side['historical_owner_assets'].values():assert digest(row['preserved'])==row['sha256']
    for n,row in aliases.items():assert sha(n)==row['sha256'],n
    proofs=read(mapping['proof_execution_bindings']['file'])['files']
    assert len(proofs)==5
    assert {n:row for n,row in ledger['proof_files'].items() if n not in proofs}==old['proof_files']
    assert ledger['declarations'][:len(old['declarations'])]==old['declarations']
    for n,row in ledger['proof_files'].items():
        ev=row['standalone_compile_evidence'];assert digest(n)==row['sha256']==ev['sha256'] and ev['exit_code']==0 and ev['source_unchanged']
        assert sha(ev['log'])==ev['log_sha256']
    for n,row in proofs.items():
        assert digest(n)==row['sha256'];assert digest(row['compiler_manifest'])==row['compiler_manifest_sha256']
        rec=read(row['compiler_manifest']);assert rec['exit_code']==0 and rec['source_unchanged']
        assert rec['source_sha256_before']==rec['source_sha256_after']==digest(n)
        assert sha(rec['log'])==rec['log_sha256'] and sha(rec['source_snapshot'])==rec['source_snapshot_sha256']==digest(n)
    exact={x['key']:x for x in inv['exercises']};units={x['key']:x for x in inv['material_source_units']}
    mapped_ex=set();mapped_units=set()
    for review in mapping['reviews']:
        ref=review['review'];assert digest(ref['file'])==ref['sha256'];r=read(ref['file'])
        assert r['reviewed_at_utc']==ref['original_review_time'] and r['reviewer']==ref['reviewer']
        for n,h in r['proof_source_sha256'].items():assert digest(n)==h
        for e in review['exercises']:
            assert exact[e['key']]['text_sha256']==e['text_sha256'];mapped_ex.add(e['key'])
        for u in review['material_units']:
            assert units[u['key']]['text_sha256']==u['text_sha256'] and units[u['key']]['source_sha256']==u['source_sha256'];mapped_units.add(u['key'])
        for ev in r['actual_standalone_evidence']:
            assert sha(ev['compiler_manifest'])==ev['compiler_manifest_sha256'] and sha(ev['raw_log'])==ev['raw_log_sha256']
    assert len(mapped_ex)==7 and len(mapped_units)==42
    oldex={e['inventory_key']:e for e in old['exercises']}
    for e in ledger['exercises']:
        actual=exact[e['inventory_key']];assert e['source_sha256']==actual['source_sha256'] and e['source_text_sha256']==actual['text_sha256']
        if e['inventory_key'] not in mapped_ex:
            restored=copy.deepcopy(e);restored.pop('source47_unchanged_literal_identity');assert restored==oldex[e['inventory_key']]
    oldclaims={c['id']:c for c in old['material_claims']}
    for c in ledger['material_claims']:
        if not set(c['source_unit_keys'])&mapped_units:
            restored=copy.deepcopy(c);restored.pop('source47_unchanged_literal_identity');assert restored==oldclaims[c['id']]
        for k in c['source_unit_keys']:
            if c['id']==k+'::claim-review':assert c['statement_in_prose']==units[k]['source_text']
    protected={}
    for number,nproof,ninput in ((18,490,2431),(19,1055,14101)):
        m=read(f'reports/full-coverage/checkpoint-{number}-manifest.json')
        assert len(m['proof_files'])==nproof and len(m['frozen_inputs_sha256'])==ninput
        for n,row in m['proof_files'].items():
            assert digest(n)==row['sha256']
            for p,h in row['evidence_sha256'].items():assert digest(p)==h
        for n,h in m['frozen_inputs_sha256'].items():assert digest(str(Path(m['snapshot'])/n))==h
        protected[str(number)]={'selected_sources':nproof,'frozen_inputs':ninput,'all_exact':True}
    return {'schema_version':1,'status':'exact_current47_unchanged_literals_and_seven_independent_practice_bindings_passed','inventory':side['current_inventory'],'identity_sidecar':mapping['unchanged_identity_sidecar'],'canonical_path_aliases':mapping['canonical_path_aliases'],'original_source44_owner_assets_preserved':side['historical_owner_assets'],'new_original_reviews_and_times':[r['review'] for r in mapping['reviews']],'counts':{'unchanged_exercises':len(oldex)-7,'new_whole_practices':7,'new_physical_units':42,'new_actual_zero_sources':5,'new_exports':34,'prior_proof_rows_preserved':len(old['proof_files'])},'protected_checkpoints':protected,'limits':['Inventory identity is separate from mathematical correspondence. Original reviews, compiler records and times are reused exactly.','Five new actual standalone-zero files await the future checkpoint aggregate/kernel audit; checkpoint19 audit does not cover them.']}
