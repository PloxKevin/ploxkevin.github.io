from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import hashlib, json, sys
R = Path('/home/oxrexkevin/SafetyBased')
sys.path.insert(0, str(R / 'book/coverage'))
from lean_names import declarations
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
ref = lambda p: {'file': str(p), 'sha256': sha(p)}
def bind(r):
    p = Path(r['file'])
    if not p.is_absolute(): p = R / p
    assert sha(p) == r['sha256'], str(p)
    return p
B = R / 'book/coverage/checks/foundations-future24/source51'
offer_p = B / 'foundations-audit24-candidate-source51-additions-draft-v1.json'
assert sha(offer_p) == '45011704cef702a8f6fb0a237342cdc91af88d833551d659a12b7234ead6c9ac'
offer = read(offer_p)
candidate_p = R / offer['mapped_ledger']
assert sha(candidate_p) == offer['mapped_ledger_sha256'] == '3446fbfe7889cdfa8c8dff485ce03f223b6662478e3d4599cd1d1850bbb7f2c9'
c = read(candidate_p)
old_p = R / offer['held23_ledger']
assert sha(old_p) == offer['held23_ledger_sha256'] == sha(R / 'book/coverage/foundations.json') == '6008c0225111ce8a8db195475036d85af95567f620e57929ea485d39e9d42279'
old = read(old_p)
interface_p = R / offer['material24_exact_interface_binding']
assert sha(interface_p) == offer['material24_exact_interface_binding_sha256'] == '95f3cf540e19ad321021d0e933431e83da28c0644242ebe5d1813ff2c933e206'
i = read(interface_p)
assert bind(i['candidate_ledger']) == candidate_p and bind(i['held_original23_ledger']) == old_p
inventory_p = bind(i['current_inventory'])
assert sha(inventory_p) == offer['current_inventory_sha256'] == sha(R / 'book/coverage/inventory.json') == 'd746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
inv = read(inventory_p); inv48 = read(R / 'book/coverage/inventory-after-correction48.json')
units = {u['key']: u for u in inv['material_source_units']}
units48 = {u['key']: u for u in inv48['material_source_units']}
own = [u for u in inv['material_source_units'] if u['source'] in old['scope_pages']]
ex = [e for e in inv['exercises'] if e['source'] in old['scope_pages']]
assert len(own) == 1756 and len(ex) == 119
assert all(u == units48[u['key']] for u in own)
ex48 = {e['key']:e for e in inv48['exercises']}
assert all(e == ex48[e['key']] for e in ex)
assert c['exercises'] == old['exercises'] and c['surrounding_prose_reviews'] == old['surrounding_prose_reviews']
assert c['source_sha256'] == old['source_sha256'] == offer['source_sha256']
for n,d in c['source_sha256'].items(): assert sha(R/n)==d
new_claim_ids = set(); removed_ids = set(); mapped_keys = set()
old_by = {r['id']:r for r in old['material_claims']}
new_by = {r['id']:r for r in c['material_claims']}
assert len(old_by)==len(old['material_claims']) and len(new_by)==len(c['material_claims'])
for row in i['material_units']:
    k = row['source_unit_key']; assert k not in mapped_keys; mapped_keys.add(k)
    assert row['entire_current51_inventory_record'] == units[k] == units48[k]
    peer = read(bind(row['original_semantic_review']))
    pr = next(u for u in peer['material_units'] if u.get('source_unit_key',u.get('key'))==k)
    assert pr == row['entire_original_whole_literal_peer_row']
    assert row['original_reviewed_at_utc'] == peer['reviewed_at_utc']
    original = [r for r in old['material_claims'] if k in r['source_unit_keys']]
    pending = [r for r in original if r['status']=='pending']
    assert pending == row['entire_original_pending_clauses'] and len(pending)==1 and pending[0]['source_unit_keys']==[k]
    assert row['retained_original_nonpending_clauses'] == [r for r in original if r['status']!='pending']
    n = row['new_candidate_claim']; assert n == new_by[n['id']]
    assert n['status']=='proved' and n['source_unit_keys']==[k] and n['remaining_gaps']==[]
    assert n['source_text']==n['statement_in_prose']==units[k]['source_text']
    assert n['source_text_sha256']==units[k]['text_sha256'] and n['source_sha256']==units[k]['source_sha256']
    assert n['hypotheses']==pr['hypotheses'] and n['lean_declarations']==pr['lean_declarations']
    assert n['correspondence']==pr.get('per_unit_reason',pr.get('reason'))
    assert n['source_review']['file']==row['original_semantic_review']['file']
    assert n['source_review']['sha256']==row['original_semantic_review']['sha256']
    assert n['source_review']['reviewed_at_utc']==peer['reviewed_at_utc']
    removed_ids.add(pending[0]['id']); new_claim_ids.add(n['id'])
assert len(mapped_keys)==6 and len(removed_ids)==6
assert set(old_by)-set(new_by)==removed_ids and set(new_by)-set(old_by)==new_claim_ids
assert [r for r in old['material_claims'] if r['id'] not in removed_ids] == [r for r in c['material_claims'] if r['id'] not in new_claim_ids]
proved = [r for r in old['material_claims'] if r['status']=='proved']
assert len(proved)==1094 and all(new_by[r['id']]==r for r in proved)
selection=read(R/offer['base_selection']);audit=read(R/offer['actual_passing_baseline_audit'])
assert sha(R/offer['base_selection'])==offer['base_selection_sha256']
assert sha(R/offer['actual_passing_baseline_audit'])==offer['actual_passing_baseline_audit_sha256']
assert selection['proof_file_count']==1131 and audit['status']=='passed' and audit['proof_file_count']==1131 and audit['theorem_count']==9193
all_names={r['name']:r['file'] for r in audit['declarations']}
new_names=[]; sources=set(); paired_records=0
for packet in i['proof_packets']:
    src=bind(packet['canonical_source']); names=[d['name'] for d in declarations(src.read_text()) if d['kind'] in ('theorem','lemma')]
    assert names==packet['public_theorem_names']
    assert str(src.relative_to(R)) not in selection['proof_files']
    sources.add(str(src.relative_to(R)));new_names.extend(names)
    for n in names: assert n not in all_names;all_names[n]=str(src.relative_to(R))
    peerp=bind(packet['original_semantic_review']);assert read(peerp)==packet['entire_original_semantic_body_and_time']
    ready=read(bind(packet['canonical_readiness']));assert ready['canonical_source']==packet['canonical_source'] and ready['original_full_semantic_peer']==packet['original_semantic_review']
    for oldname,alias in packet['all_original_TMP_byte_copies'].items(): assert Path(oldname).read_bytes()==bind(alias).read_bytes()
    ev={};commands=set()
    for pair in packet['actual_pair']:
        rp=bind(pair['reference']);a=read(rp);assert a==pair['entire_original_actual_record_and_time']
        lp=bind(pair['raw_log']);sp=bind(pair['source_snapshot'])
        assert a['actual_exit_code']==0 and a['source_sha256_before']==a['source_sha256_after']==sha(src)==sha(sp)
        assert a['actual_command'] in [['lake','build','SafeLearning.'+src.stem],['lake','env','lean','SafeLearning/'+src.name]]
        assert a['actual_workdir']==str(R/'verification/lean') and a['log_sha256']==sha(lp)
        commands.add(a['actual_command'][1]);paired_records+=1
        for p in [rp,lp,sp]:ev[str(p.relative_to(R))]=sha(p)
    assert commands=={'build','env'}
    assert offer['proof_files'][str(src.relative_to(R))]['sha256']==sha(src)
    assert offer['proof_files'][str(src.relative_to(R))]['evidence_sha256']==ev
assert len(sources)==5 and len(new_names)==len(set(new_names))==37 and paired_records==10
assert set(offer['proof_files'])==sources==set(offer['new_proof_sources_for_checkpoint24'])
referenced={all_names[n] for row in i['material_units'] for n in row['new_candidate_claim']['lean_declarations']}
selected_referenced=referenced-sources
assert i['referenced_existing_selected23_proof_sources']=={n:selection['proof_files'][n]['sha256'] for n in selected_referenced}
assert set(c['proof_files'])==set(old['proof_files'])|sources|selected_referenced
for n,d in old['proof_sha256'].items():assert c['proof_sha256'][n]==d
for n in c['proof_files']:assert sha(R/n)==c['proof_sha256'][n]
for k,v in old.items():
    if k not in ['proof_files','proof_sha256','material_claims','counts','limits']:
        assert c[k]==v,k
assert c['counts']['material_claim_statuses']==dict(Counter(r['status'] for r in c['material_claims']))
assert c['counts']['exercise_statuses']==old['counts']['exercise_statuses']
assert c['limits'][:len(old['limits'])]==old['limits'] and len(c['limits'])==len(old['limits'])+1
def physical(j):
    d={}
    for r in j['material_claims']:
        for k in r['source_unit_keys']:d.setdefault(k,set()).add(r['status'])
    c=Counter('pending' if 'pending' in v else 'not_a_formal_claim' if v=={'not_a_formal_claim'} else 'proved' for v in d.values())
    return {'total':len(d),'whole_proved':c['proved'],'nonformal':c['not_a_formal_claim'],'whole_pending':c['pending']}
assert physical(old)==i['physical_before']=={'total':1756,'whole_proved':762,'nonformal':524,'whole_pending':470}
assert physical(c)==i['physical_after']==offer['material_counts']=={'total':1756,'whole_proved':768,'nonformal':524,'whole_pending':464}
builder_p=R/offer['current_owner_builder'];assert sha(builder_p)==offer['current_owner_builder_sha256']=='1bf9dcf16548c7df77d2c0bed8292fcc78d41d9aeac71a4ecc5cbd80a83a90ee'
actual_p=B/'candidate-builder-actual-execution-source51-v1.json';actual=read(actual_p)
assert actual['actual_exit_code']==0 and actual['status']=='passed' and actual['actual_command']==['python',str(builder_p)]
assert actual['actual_workdir']==str(R) and actual['actual_helper_sha256_before']==actual['actual_helper_sha256_after']==sha(builder_p)
assert sha(R/actual['raw_log'])==actual['raw_log_sha256']
for n,row in selection['proof_files'].items():assert sha(R/n)==row['sha256']
manifest=read(R/'reports/full-coverage/checkpoint-23-manifest.json')
for n,d in manifest['working_inputs_sha256'].items():
    if n.startswith('SafeLearning/') or n in ['book/coverage/'+o+'.json' for o in ['core','foundations','applied','modules','applied-promotions']]:assert sha(R/n)==d
out={'status':'independent_exact_six_whole_literal_foundation24_isolated_candidate_mechanical_confirmation_passed','reviewer':'/root/modules_resume','checked_at_utc':datetime.now(timezone.utc).isoformat(),'errors':[],'candidate_ledger':ref(candidate_p),'original_draft_offer':ref(offer_p),'exact_interface':ref(interface_p),'actual_candidate_builder':ref(builder_p),'actual_candidate_execution':ref(actual_p),'actual_candidate_raw_log':ref(R/actual['raw_log']),'whole_unit_keys':sorted(mapped_keys),'new_proof_sources':sorted(sources),'new_public_export_count':37,'genuine_paired_zero_record_count':10,'all119_original_exercise_bodies_exact':True,'all1094_prior_proved_atoms_exact':True,'all_other_material_bodies_exact':True,'original_semantic_decisions_reasons_hypotheses_names_and_times_exact':True,'all1131_selected23_sources_and_live_owners_exact':True,'physical_before':physical(old),'physical_after':physical(c),'narrow_three_source_canonical_binding':ref(Path('/tmp/foundations-three-canonical-sources-original-module-peers-binding24-v1.json')),'checker':ref(Path(__file__)),'scope':'Read-only isolated candidate mechanics only. Author builder execution is genuine recorded provenance and is not rerun. No live owner installation, new semantic decision, aggregate24, source correction or checkpoint24 selection inferred.'}
target=Path('/tmp/foundations24-six-whole-literal-candidate-independent-modules-confirmation-v1.json');assert not target.exists();target.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'peer':ref(target)}))
