"""Check source48 identity and eight literal Viability mappings against immutable20."""
from pathlib import Path
import copy,hashlib,json

def check_bindings(root,ledger,old,side,mapping):
    cache={}
    def digest(n):
        p=root/n;st=p.stat();key=(str(p),st.st_size,st.st_mtime_ns)
        if key not in cache:cache[key]=hashlib.sha256(p.read_bytes()).hexdigest()
        return cache[key]
    def read(n):return json.loads((root/n).read_text())
    aliases=read(mapping['canonical_path_aliases']['file'])['aliases']
    def resolve(n):
        s=aliases.get(n,{}).get('path',n);p=Path(s)
        assert not p.is_absolute() and '..' not in p.parts and str(p)==s,n
        return s
    def actual_record(n,h,source):
        assert digest(n)==h
        r=read(n);assert r['exit_code']==0 and r['source_sha256_before']==r['source_sha256_after']==digest(source)
        assert digest(resolve(r['log']))==r['log_sha256'];return r
    assert digest('book/coverage/inventory.json')==side['current_inventory']['sha256']==mapping['inventory_sha256']
    assert digest(side['current_inventory']['file'])==side['current_inventory']['sha256']
    assert digest(side['historical_inventory']['file'])==side['historical_inventory']['sha256']
    inv=read(side['current_inventory']['file']);historical=read(side['historical_inventory']['file'])
    for section in ('exercises','material_source_units'):
        a={x['key']:x for x in historical[section] if x['source'] in old['scope_pages']}
        b={x['key']:x for x in inv[section] if x['source'] in old['scope_pages']}
        assert a==b and {x['key']:x for x in side['unchanged_owned_literals'][section]}==a
        assert side['changed_owned_literals_excluded'][section]==[]
    for row in side['historical_owner_assets'].values():assert digest(row['preserved'])==row['sha256']
    proofrows=read(mapping['proof_execution_bindings']['file'])['files'];assert len(proofrows)==5
    assert {n:r for n,r in ledger['proof_files'].items() if n not in proofrows}==old['proof_files']
    assert ledger['declarations'][:len(old['declarations'])]==old['declarations']
    supplied=mapping['explicit_cross_owner_proof_offer'];assert digest(supplied['file'])==supplied['sha256']
    supplied=read(supplied['file']);assert set(supplied['proof_files'])==set(proofrows)
    for n,p in proofrows.items():
        assert digest(n)==p['sha256']==supplied['proof_files'][n]['sha256']
        actual_record(p['compiler_manifest'],p['compiler_manifest_sha256'],n)
        actual_record(p['named_manifest'],p['named_manifest_sha256'],n)
        assert ledger['proof_files'][n]['declarations']==p['declarations']
    for n,p in ledger['proof_files'].items():
        ev=p['standalone_compile_evidence'];assert digest(n)==p['sha256']==ev['sha256'] and ev['exit_code']==0 and ev['source_unchanged']
        assert digest(resolve(ev['log']))==ev['log_sha256']
    es={x['key']:x for x in inv['exercises']};us={x['key']:x for x in inv['material_source_units']};mappedex=set();mappedu=set()
    for batch in mapping['reviews']:
        ref=batch['review'];assert digest(ref['file'])==ref['sha256'];r=read(ref['file'])
        assert r['reviewed_at_utc']==ref['original_review_time'] and r['reviewed_by']==ref['reviewer']
        original={e['exercise_key']:e for e in r['reviewed_exercises']};originalu={u['source_unit_key']:u for e in r['reviewed_exercises'] for u in e['material_units']}
        for e in batch['exercises']:
            key=e['key'];o=original[key];a=es[key];assert key not in mappedex;mappedex.add(key)
            assert o['whole_exercise_approved'] is True and o['missing_clauses']==[]
            assert e['text_sha256']==o['exercise_text_sha256']==a['text_sha256'] and o['source_text']==a['source_text']
            assert e['lean_declarations']==o['lean_declarations'] and e['hypotheses']==o['hypotheses'] and e['reviewed_clauses']==o['reviewed_clauses']
        for u in batch['material_units']:
            key=u['key'];o=originalu[key];a=us[key];assert key not in mappedu;mappedu.add(key)
            assert u['text_sha256']==o['unit_text_sha256']==a['text_sha256'] and u['source_sha256']==o['source_sha256']==a['source_sha256']
            assert o['source_text']==a['source_text'] and o['missing_clauses']==[]
            assert u['status']=={'proved':'proved','not_formalizable':'not_a_formal_claim'}[o['material_status']]
            assert u['lean_declarations']==o['lean_declarations'] and u['hypotheses']==o['hypotheses'] and u['reason']==o['per_unit_reason']
    assert len(mappedex)==8 and len(mappedu)==40
    oldex={e['inventory_key']:e for e in old['exercises']};oldc={c['id']:c for c in old['material_claims']}
    for e in ledger['exercises']:
        a=es[e['inventory_key']];assert e['source_sha256']==a['source_sha256'] and e['source_text_sha256']==a['text_sha256']
        if e['inventory_key'] not in mappedex:
            restored=copy.deepcopy(e);restored.pop('source48_unchanged_literal_identity');assert restored==oldex[e['inventory_key']]
    for c in ledger['material_claims']:
        if c['id'] not in {k+'::claim-review' for k in mappedu}:
            restored=copy.deepcopy(c);restored.pop('source48_unchanged_literal_identity');assert restored==oldc[c['id']]
    protections={}
    for number,np,ni in ((19,1055,14101),(20,1068,30207)):
        m=read(f'reports/full-coverage/checkpoint-{number}-manifest.json');assert len(m['proof_files'])==np and len(m['frozen_inputs_sha256'])==ni
        for n,p in m['proof_files'].items():
            assert digest(n)==p['sha256']
            for a,h in p['evidence_sha256'].items():assert digest(a)==h
        for a,h in m['frozen_inputs_sha256'].items():assert digest(str(Path(m['snapshot'])/a))==h
        protections[str(number)]={'sources':np,'frozen_inputs':ni,'all_exact':True}
    return {'schema_version':1,'status':'exact_current48_unchanged_literals_and_eight_independent_viability_bindings_passed',
      'inventory':side['current_inventory'],'identity_sidecar':mapping['unchanged_identity_sidecar'],'review_mapping_sha256':digest('book/coverage/checks/modules-future21/source48/review-mappings-v1.json'),
      'counts':{'whole_exercises':8,'physical_units':40,'applied_supplied_sources':5,'new_exports':34,'old_proof_rows':len(old['proof_files'])},'protected_checkpoints':protections,
      'limits':['Independent semantic reviews and their original times are reused verbatim. Identity normalization does not itself approve mathematics.','Applied21 selects the five supplied source-matched actual-zero files; the future21 aggregate/kernel audit remains separate.']}
