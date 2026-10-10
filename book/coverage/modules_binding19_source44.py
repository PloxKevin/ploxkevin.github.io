"""Check current literal identities without rewriting historical semantic reviews."""
import hashlib
import json
from pathlib import Path

def check_bindings(root,ledger,inventory,old,side,mapping):
    aliases=json.loads((root/mapping['canonical_path_aliases']['file']).read_text())['aliases']
    def resolve(path):
        value=aliases.get(str(path),{}).get('path',str(path))
        p=root/value
        assert not Path(value).is_absolute() and '..' not in p.parts and p.is_relative_to(root),path
        return p
    def digest(path):return hashlib.sha256(resolve(path).read_bytes()).hexdigest()
    def read(path):return json.loads(resolve(path).read_text())
    assert digest('book/coverage/inventory.json')==side['current_inventory']['sha256']==mapping['inventory_sha256']
    assert inventory==read(side['current_inventory']['file'])
    assert digest(side['historical_inventory']['file'])==side['historical_inventory']['sha256']
    historical=read(side['historical_inventory']['file'])
    for section in ['exercises','material_source_units']:
        before={r['key']:r for r in historical[section]};after={r['key']:r for r in inventory[section]}
        for identity in side['unchanged_owned_literals'][section]:
            k=identity['key'];assert {f:v for f,v in before[k].items() if f!='source_sha256'}=={f:v for f,v in after[k].items() if f!='source_sha256'},k
            assert after[k]['source_sha256']==digest(after[k]['source'])
        changed={r['key'] for r in side['changed_owned_literals_excluded'][section]}
        assert changed=={k for k,a in before.items() if a['source'] in ledger['scope_pages'] and a['source_text']!=after[k]['source_text']}
    for path,row in aliases.items():assert digest(row['path'])==row['sha256'],path
    for r in side['original_semantic_review_bodies_times_preserved']:
        assert digest(r['review'])==r['review_sha256']
        raw=read(r['review']);assert raw.get('reviewed_at_utc')==r['original_review_time_unchanged']
    compiler={}
    for p,h in side['raw_compiler_manifests'].items():
        assert digest(p)==h;raw=read(p);rows=raw.get('files',[raw]);assert rows
        for row in rows:
            assert row['exit_code']==0
            src=row.get('file',row.get('source'));hsrc=row.get('sha256',row.get('source_sha256_after',row.get('sha256_after')))
            assert digest(src)==hsrc,(p,src)
            assert row.get('source_unchanged',True)
            for k in ['source_sha256_before','sha256_before']:
                if k in row:assert row[k]==hsrc
            assert digest(row['log'])==row['log_sha256']
        compiler[p]=h
    assert ledger['proof_files']==old['proof_files'] and ledger['declarations']==old['declarations']
    for p,row in ledger['proof_files'].items():
        e=row['standalone_compile_evidence'];assert digest(p)==row['sha256']==e['sha256'] and e['exit_code']==0 and e['source_unchanged']
        assert digest(e['log'])==e['log_sha256']
    current={r['key']:r for r in inventory['exercises']};units={r['key']:r for r in inventory['material_source_units']}
    for e in ledger['exercises']:
        r=current[e['inventory_key']];assert e['source_sha256']==r['source_sha256'] and e['source_text_sha256']==r['text_sha256']
    for c in ledger['material_claims']:
        for key in c['source_unit_keys']:
            assert units[key]['source'] in ledger['scope_pages']
            if c['id']==key+'::claim-review':assert c['statement_in_prose']==units[key]['source_text']
    review_rows=[]
    for r in mapping['reviews']:
        ref=r['review'];assert digest(ref['file'])==ref['sha256'];raw=read(ref['file'])
        assert raw['reviewer']==ref['reviewer'] and raw['reviewed_at_utc']==ref['original_review_time']
        for p,h in raw.get('proof_source_sha256',{}).items():assert digest(p)==h,(ref['file'],p)
        for e in r['exercises']:assert current[e['key']]['text_sha256']==e['text_sha256']
        for u in r['material_units']:assert units[u['key']]['text_sha256']==u['text_sha256']
        for evidence in raw.get('actual_standalone_evidence',[]):
            manifest=evidence.get('compiler_manifest')
            if not manifest:continue
            assert digest(manifest)==evidence['compiler_manifest_sha256']
            record=read(manifest)
            for row in record.get('files',[record]):
                assert row['exit_code']==0
                src=row.get('file',row.get('source'));h=row.get('sha256',row.get('source_sha256_after',row.get('sha256_after')))
                assert digest(src)==h and digest(row['log'])==row['log_sha256']
            compiler[manifest]=evidence['compiler_manifest_sha256']
        review_rows.append(ref)
    s=read('reports/full-coverage/checkpoint-18-selection.json');protected={}
    for p,r in s['proof_files'].items():protected[p]=r['sha256'];protected.update(r['evidence_sha256'])
    assert len(s['proof_files'])==490 and len(protected)==565
    for p,h in protected.items():assert digest(p)==h
    f=read('reports/full-coverage/checkpoint-18-manifest.json');assert len(f['frozen_inputs_sha256'])==2431
    for p,h in f['frozen_inputs_sha256'].items():assert digest(str(Path(f['snapshot'])/p))==h
    return {'schema_version':1,'status':'exact_current44_unchanged_literal_fresh_review_and_actual_execution_bindings_passed','current_inventory':side['current_inventory']['file'],'current_inventory_sha256':side['current_inventory']['sha256'],'identity_sidecar':mapping['unchanged_identity_sidecar'],'canonical_path_aliases':mapping['canonical_path_aliases'],'referenced_original_reviews_preserved':side['original_semantic_review_bodies_times_preserved'],'referenced_fresh_or_unchanged_reviews':review_rows,'raw_compiler_manifests':compiler,'proof_files':side['proof_files'],'protected_selected_sources':490,'protected_source_evidence_paths':565,'frozen18_inputs':2431,'exercise_count':len(ledger['exercises']),'material_claim_count':len(ledger['material_claims']),'limits':['Every changed whole literal was excluded before fresh review mapping. Original semantic bodies/time/hypotheses/gaps are historical immutable evidence.','Actual original compiler/log records are reused exactly, without a new compiler success assertion. Aggregate kernel/axiom verification remains a separate root check.']}
