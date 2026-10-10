#!/usr/bin/env python3
from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import hashlib, json, re, sys

ROOT = Path('/home/oxrexkevin/SafetyBased')
sys.path.insert(0, str(ROOT/'book/coverage'))
from lean_names import declarations
cache = {}
def sha(name):
    if name not in cache:
        cache[name] = hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    return cache[name]
def read(name):
    return json.loads((ROOT/name).read_text())
def exact(mapping):
    for name,digest in mapping.items():
        assert sha(name)==digest,(name,digest,sha(name))
def actual_record(source,digest,evidence):
    matches=[]
    for name in evidence:
        if not name.endswith('.json'): continue
        doc=read(name)
        rows=doc.get('files',[doc]) if isinstance(doc,dict) else []
        for row in rows:
            if not isinstance(row,dict) or row.get('exit_code')!=0: continue
            if row.get('source',row.get('file'))!=source: continue
            after=row.get('source_sha256_after',row.get('sha256_after',row.get('source_sha256',row.get('sha256'))))
            before=row.get('source_sha256_before',row.get('sha256_before',after))
            if (before,after)!=(digest,digest): continue
            assert row.get('source_unchanged',True)
            cmd=row.get('command',row.get('actual_command',doc.get('actual_command')))
            assert isinstance(cmd,list) and Path(cmd[0]).name=='lake',(source,cmd)
            assert cmd[1:3] in [['env','lean'],['build','SafeLearning.'+Path(source).stem]],(source,cmd)
            assert row.get('actual_workdir',row.get('workdir',doc.get('actual_workdir',doc.get('workdir'))))
            logdigest=row.get('log_sha256')
            assert logdigest and logdigest in evidence.values(),(source,row.get('log'))
            logpaths=[n for n,h in evidence.items() if h==logdigest and n.endswith('.log')]
            assert logpaths,(source,logdigest)
            matches.append(dict(record=name,log_paths=logpaths,log_sha256=logdigest,command=cmd))
    assert matches,source
    return matches

selection_name='reports/full-coverage/checkpoint-19-selection.json'
s=read(selection_name)
assert sha(selection_name)=='9fcf2c8d8785e1b1e98fa482d47a4a4dda2fb5f19ae9d8375e860f32767e4672'
assert s['coverage_complete'] is False and not s['deliberate_baseline_source_revisions']
assert s['status']=='explicit_current44_source_matched_selection_requires_fresh_aggregate_audit'
baseline=read(s['baseline_selection']); audit=read(s['actual_passing_baseline_audit'])
assert sha(s['baseline_selection'])==s['baseline_selection_sha256']
assert sha(s['actual_passing_baseline_audit'])==s['actual_passing_baseline_audit_sha256']
assert audit['status']=='passed' and len(baseline['proof_files'])==490
assert audit['proof_sha256']=={n:r['sha256'] for n,r in baseline['proof_files'].items()}
expected={n:r['sha256'] for n,r in baseline['proof_files'].items()}
for n,r in baseline['proof_files'].items():
    assert s['proof_files'][n]['sha256']==r['sha256']
    assert not set(r['evidence_sha256'].items())-set(s['proof_files'][n]['evidence_sha256'].items())

offers={}
for name,digest in s['offers_sha256'].items():
    assert sha(name)==digest
    offers[name]=read(name)
assert len(offers)==4
offer_rows=Counter()
for name,o in offers.items():
    if 'applied-audit' in name:
        assert sha(o['mapped_ledger'])==o['mapped_ledger_sha256']
        assert sha('book/coverage/applied-promotions.json')==o['mapped_promotions_sha256']
        exact(o['independent_source_reviews'])
        assert o['inventory_sha256']==s['current_inventory_sha256']
        rows={r['source']:r['sha256_after'] for r in o['modules']}
        for r in o['modules']:
            assert r['exit_code']==0 and r['sha256_before']==r['sha256_after']
    else:
        key='module_ledger' if 'modules-audit' in name else 'mapped_ledger'
        assert sha(o[key])==o[key+'_sha256']
        assert o['current_inventory_sha256']==s['current_inventory_sha256']
        rows={n:r['sha256'] for n,r in o['proof_files'].items()}
    exact(o['source_sha256'])
    for n,d in rows.items():
        if n in expected: assert expected[n]==d
        expected[n]=d
    offer_rows[name]=len(rows)
assert expected=={n:r['sha256'] for n,r in s['proof_files'].items()}
assert len(expected)==s['proof_file_count']==1055
assert len(set(expected)-set(baseline['proof_files']))==s['new_file_count']==565
exact({n:r['sha256'] for n,r in s['proof_files'].items()})
all_evidence={}
new_actual={}
for n,r in s['proof_files'].items():
    exact(r['evidence_sha256'])
    all_evidence.update(r['evidence_sha256'])
    if n not in baseline['proof_files']:
        new_actual[n]=actual_record(n,r['sha256'],r['evidence_sha256'])
        assert r['original_actual_zero_record'] in {m['record'] for m in new_actual[n]}

all_names=set(); imports=[]
for n in expected:
    body=(ROOT/n).read_text()
    all_names.update(d['name'] for d in declarations(body))
    for line in re.findall(r'^import[^\n]*',body,re.M):
        for dep in line.split()[1:]:
            if dep.startswith('SafeLearning.'):
                depname='verification/lean/'+dep.replace('.','/')+'.lean'
                assert depname in expected,(n,depname)
                imports.append((n,depname))

g=read(s['global_integrity'])
assert sha(s['global_integrity'])==s['global_integrity_sha256']
assert g['integrity_status']=='passed' and not g['errors']
assert g['inventory_sha256']==s['current_inventory_sha256']
assert sha(s['current_inventory'])==sha('book/coverage/inventory.json')==s['current_inventory_sha256']
statuses=Counter(); claims=0
for row in g['domains']:
    name='book/coverage/'+row['domain']+'.json'
    assert sha(name)==row['ledger_sha256']
    ledger=read(name)
    statuses.update(e['status'] for e in ledger['exercises'])
    for claim in ledger['material_claims']+[c for e in ledger['exercises'] for c in e['claims']]:
        assert set(claim['lean_declarations'])<=all_names,(row['domain'],claim['id'])
        claims+=1
assert statuses==Counter(complete_math=475,partial=17,pending=64)
assert {f'exercise:{n}':v for n,v in statuses.items()}=={n:v for n,v in g['counts']['statuses'].items() if n.startswith('exercise:')}
exact(g['source_sha256'])
exact(s['independent_current44_confirmations_sha256'])

module=next(o for n,o in offers.items() if 'modules-audit' in n)
depref=module['canonical_dependency_manifest']
assert sha(depref['file'])==depref['sha256']
dep=read(depref['file'])
external=[r for r in dep['artifacts'] if r['type']=='external_primary_paper_reference']
external_hashes={r['sha256'] for r in external}
assert len(external)==11
assert all(not r['required_for_execution_or_immutable_provenance_freeze'] for r in external)
required={r['path']:r['sha256'] for r in dep['artifacts'] if r['required_for_execution_or_immutable_provenance_freeze'] and Path(r['path']).suffix in {'.txt','.cjs'}}
assert len(required)==49
assert Counter(Path(n).suffix for n in required)==Counter({'.txt':45,'.cjs':4})
assert len(s['extra_frozen_inputs'])==2890
for n,r in s['extra_frozen_inputs'].items():
    p=Path(n)
    assert not p.is_absolute() and '..' not in p.parts and str(p)==n
    assert sha(n)==r['sha256']
    assert r['sha256'] not in external_hashes,(n,'full reference was included')
for n,d in required.items(): assert s['extra_frozen_inputs'][n]['sha256']==d
excluded_history=[]
for p in (ROOT/'reports/full-coverage/source-history').rglob('*'):
    if p.is_file() and p.suffix in {'.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt'}:
        n=str(p.relative_to(ROOT));d=sha(n)
        if d in external_hashes:
            assert n not in s['extra_frozen_inputs']
            excluded_history.append(n)
        else: assert s['extra_frozen_inputs'][n]['sha256']==d
assert len(excluded_history)==13
manifest_name='reports/full-coverage/checkpoint-18-manifest.json'; m=read(manifest_name)
assert len(m['frozen_inputs_sha256'])==2431
first=s['proof_files'][sorted(s['proof_files'])[0]]['evidence_sha256']
for n,d in m['frozen_inputs_sha256'].items():
    old=m['snapshot']+'/'+n
    assert sha(old)==d and first[old]==d
assert first[manifest_name]==sha(manifest_name)
assert first[s['baseline_selection']]==sha(s['baseline_selection'])
prep='book/coverage/checks/checkpoint19-selection-preparation-v3.json'; p=read(prep)
assert p['actual_exit_code']==0
assert sha('book/coverage/prepare_checkpoint19_selection.py')==p['helper_sha256']
assert sha(p['log'])==p['log_sha256']

out=dict(schema_version=1,reviewed_at_utc=datetime.now(timezone.utc).isoformat(),
    status='independent_current44_selection19_exact_proof_evidence_import_offer_and_extra_input_review_passed',
    reviewer='/root/modules_resume',selection=selection_name,selection_sha256=sha(selection_name),
    preparation_helper='book/coverage/prepare_checkpoint19_selection.py',preparation_helper_sha256=p['helper_sha256'],
    original_preparation=prep,original_preparation_sha256=sha(prep),
    inventory=s['current_inventory'],inventory_sha256=s['current_inventory_sha256'],
    offers_sha256=s['offers_sha256'],offer_rows=dict(offer_rows),proof_count=1055,new_proof_count=565,
    original_actual_zero_records=new_actual,distinct_evidence_paths=len(all_evidence),
    local_import_edges=len(imports),resolved_public_declarations=len(all_names),referenced_claim_rows=claims,
    global_integrity=s['global_integrity'],global_integrity_sha256=s['global_integrity_sha256'],
    exact_whole_partial_pending=dict(statuses),required_located_txt_cjs_sha256=required,
    extra_input_count=2890,full_external_reference_count=11,excluded_duplicate_external_history_paths=excluded_history,
    previous_frozen18_input_count=2431,previous_frozen18_provenance_exact=True,
    review_notes=['Independently reconstructed the exact four-offer plus retained490 source union.',
      'Original actual source-matched zero compiler records, exact raw-log bytes and historical execution times remain immutable.',
      'Every local SafeLearning import and mapped declaration resolves within the selected source set.',
      'All required45 located text excerpts and4 harnesses are explicit inputs; eleven full references and13 duplicate histories remain external.',
      'Old2431 frozen input bytes, baseline selection and baseline audit are preserved only as provenance.'],
    limits=['Read-only identity/evidence/import/coverage review; no new Lean compilation or aggregate/kernel/axiom audit claimed.',
      '475 whole exercises does not claim full coverage:17 partial,64 pending and8907 material units pending remain.',
      'Existing browser observation is separately recorded by root; this report does not create a new browser execution.'])
destination=Path('/tmp/modules-checkpoint19-final-selection44-independent-review-v1.json')
assert not destination.exists()
destination.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],file=str(destination),sha256=hashlib.sha256(destination.read_bytes()).hexdigest(),proofs=1055,new=565,extras=2890,evidence_paths=len(all_evidence))))
