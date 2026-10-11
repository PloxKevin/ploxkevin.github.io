"""Isolated four-whole-literal Foundation25 candidate with exact prior24 bodies."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import copy,hashlib,json,re
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'book/coverage/checks/foundations-future25/source52'
PACK=ROOT/'book/coverage/checks/foundations-future25/material-batch1/two-source31-export-actual-canonical-readiness25-v1.json'
PACK_SHA='fb000de1d12fa918106cc181ca07cad500bfbc2d1e167a3b0533fafdae8f4375'
OLD=ROOT/'book/coverage/foundations.json';OLD_SHA='e3ff8460281d2a745c6def2d007b6465a1b5c352a1e14d90d486dec64835982b'
INV=ROOT/'book/coverage/inventory-after-correction52.json';INV_SHA='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
SELECTION=ROOT/'reports/full-coverage/checkpoint-24-selection.json';SEL_SHA='9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314'
AUDIT=ROOT/'reports/full-coverage/lean-checkpoint-24/verification-original.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def rel(p):return p.relative_to(ROOT).as_posix()
def ref(p):return {'file':rel(p),'sha256':sha(p)}
def bind(r):
    p=ROOT/r['file'];assert sha(p)==r['sha256'],r['file'];return p
def write(p,d):
    with p.open('x') as f:json.dump(d,f,ensure_ascii=False,indent=2);f.write('\n')
def physical(d):
    by={}
    for row in d['material_claims']:
        for k in row['source_unit_keys']:by.setdefault(k,set()).add(row['status'])
    c=Counter('pending' if 'pending' in s else 'not_a_formal_claim' if s=={'not_a_formal_claim'} else 'proved' for s in by.values())
    return {'total':len(by),'whole_proved':c['proved'],'nonformal':c['not_a_formal_claim'],'whole_pending':c['pending']}
assert sha(OLD)==OLD_SHA and sha(INV)==sha(ROOT/'book/coverage/inventory.json')==INV_SHA
assert sha(PACK)==PACK_SHA and sha(SELECTION)==SEL_SHA
old=read(OLD);inv=read(INV);manifest=read(ROOT/'reports/full-coverage/checkpoint-24-manifest.json');audit=read(AUDIT)
assert manifest['status']=='formal_verification_passed_partial_coverage' and manifest['selection_sha256']==SEL_SHA
assert len(manifest['proof_files'])==audit['proof_file_count']==1144 and audit['theorem_count']==9279 and audit['status']=='passed'
assert manifest['successful_verification']['report_sha256']==sha(AUDIT)
for stem in ['verify-checkpoint24-execution-v1','export-checkpoint24-execution-v1']:
    a=read(ROOT/'reports/full-coverage'/f'{stem}.json')
    assert a['actual_exit_code']==0 and sha(ROOT/a['log'])==a['log_sha256']
selected={n:r['sha256'] for n,r in manifest['proof_files'].items()}
assets={n:d for n,d in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
owners={n:manifest['working_inputs_sha256'][n] for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
protected={**selected,**assets,**owners,**old['source_sha256'],rel(INV):INV_SHA,'book/coverage/inventory.json':INV_SHA,rel(SELECTION):SEL_SHA}
def guard():
    for n,d in protected.items():assert sha(ROOT/n)==d,n
    for n,d in {**selected,**assets}.items():assert sha(ROOT/'reports/full-coverage/checkpoint-24'/n)==d,n
guard();BASE.mkdir(parents=True,exist_ok=True)
CAND=BASE/'foundations25-candidate-source52-v1.json'
INTERFACE=BASE/'foundations25-four-complete-literal-interface-source52-v1.json'
DRAFT=BASE/'foundations-audit25-candidate-source52-additions-draft-v1.json'
INTEGRITY=BASE/'candidate-original24-preservation-source52-v1.json'
HELD=BASE/'held-foundations24-original-source52-v1.json'
assert not any(p.exists() for p in [CAND,INTERFACE,DRAFT,INTEGRITY,HELD])
with HELD.open('xb') as f:f.write(OLD.read_bytes())
units={u['key']:u for u in inv['material_source_units'] if u['source'] in old['scope_pages']}
exercises={u['key']:u for u in inv['exercises'] if u['source'] in old['scope_pages']}
assert len(units)==1756 and len(exercises)==119
inv48=read(ROOT/'book/coverage/inventory-after-correction48.json')
u48={u['key']:u for u in inv48['material_source_units']};e48={e['key']:e for e in inv48['exercises']}
assert all(u==u48[k] for k,u in units.items()) and all(e==e48[k] for k,e in exercises.items())
candidate=copy.deepcopy(old);pack=read(PACK)
assert pack['source_count']==2 and pack['public_theorem_count']==31 and pack['whole_mathematical_unit_count']==4
decl_files={d['name']:d['file'] for d in audit['declarations']};assert len(decl_files)==9279
newproofs={};newnames=set();packets=[];mappings=[];removedids=set();mappedkeys=set();covered=set()
semanticrefs={};actualrefs={};readyrefs={};allaliases={};referenced_selected={}
for gr in pack['groups']:
    gp=bind(gr);g=read(gp);readyrefs[rel(gp)]=sha(gp);src=bind(g['canonical_source']);text=src.read_text()
    namespace=re.search(r'^namespace (\S+)',text,re.M)[1]
    names=[namespace+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
    assert names==g['public_theorem_names'] and len(names)==g['public_theorem_count']
    assert not re.search(r'\b(sorry|admit|axiom)\b',text) and rel(src) not in selected and rel(src) not in old['proof_files']
    assert not newnames.intersection(names);newnames.update(names)
    for n in names:decl_files[n]=rel(src)
    peerp=bind(g['original_full_semantic_peer']);peer=read(peerp)
    assert peer==g['entire_original_full_semantic_peer_body_and_time'] and 'passed' in peer['status'] and peer['errors']==[]
    semanticrefs[rel(peerp)]=sha(peerp)
    for n,r in g['all_original_TMP_byte_aliases'].items():
        cp=bind(r);assert cp.read_bytes()==Path(n).read_bytes(),n
        if n in allaliases:assert allaliases[n]['sha256']==r['sha256']
        allaliases[n]=r
    evidence={};pairs=[]
    for pr in g['actual_canonical_pair']:
        rp=bind(pr['actual_record']);a=read(rp);log=bind(pr['raw_log']);snapshot=bind(pr['source_snapshot'])
        exits=[a[k] for k in ['actual_exit_code','exit_code'] if k in a];assert exits and all(type(x)is int and x==0 for x in exits)
        assert a['actual_workdir']==str(ROOT/'verification/lean') and a['source']==rel(src)
        assert a['actual_command'] in [['lake','build','SafeLearning.'+src.stem],['lake','env','lean','SafeLearning/'+src.name]]
        assert a['source_sha256_before']==a['source_sha256_after']==sha(src)==sha(snapshot)
        assert a['log_sha256']==sha(log) and a['log']==rel(log) and a['source_snapshot']==rel(snapshot)
        assert a['source_snapshot_sha256']==sha(snapshot) and a['started_at_utc']<a['finished_at_utc'] and a['elapsed_seconds']>0
        helper=ROOT/a['actual_pair_helper'];assert sha(helper)==a['actual_pair_helper_sha256'] and ref(helper)==g['actual_helper']
        evidence.update({rel(rp):sha(rp),rel(log):sha(log),rel(snapshot):sha(snapshot)})
        actualrefs[rel(rp)]=sha(rp);pairs.append({'reference':ref(rp),'entire_original_actual_record_and_time':a,'raw_log':ref(log),'source_snapshot':ref(snapshot)})
    assert len(pairs)==2 and {p['entire_original_actual_record_and_time']['actual_command'][1] for p in pairs}=={'env','build'}
    newproofs[rel(src)]={'sha256':sha(src),'evidence_sha256':evidence,
        'evidence_scope':'Genuine source-exact canonical standalone and named target EXIT0 with raw logs and snapshot. Original complete semantic bodies/time retained; future25 aggregate and selection remain separate.'}
    candidate['proof_files'].append(rel(src));candidate['proof_sha256'][rel(src)]=sha(src)
    packets.append({'group':g['group'],'canonical_source':ref(src),'public_theorem_names':names,'original_semantic_review':ref(peerp),
        'entire_original_semantic_body_and_time':peer,'canonical_readiness':ref(gp),'actual_pair':pairs,'all_original_TMP_byte_aliases':g['all_original_TMP_byte_aliases']})
    for row in peer['material_units']:
        key=row['key'];unit=units[key]
        assert row['inventory_record']==unit==u48[key] and key not in mappedkeys;mappedkeys.add(key)
        assert row['whole_material_unit_approved'] is True and row['missing']==[]
        reason=row['reason'];hypotheses=row['hypotheses'];declarations=row['decls']
        assert isinstance(reason,str) and reason and declarations
        for n in declarations:
            assert n in decl_files,n
            p=ROOT/decl_files[n]
            if rel(p) in newproofs:assert sha(p)==newproofs[rel(p)]['sha256']
            else:
                assert sha(p)==selected[rel(p)]
                referenced_selected[rel(p)]=selected[rel(p)]
                if rel(p) not in candidate['proof_files']:candidate['proof_files'].append(rel(p));candidate['proof_sha256'][rel(p)]=sha(p)
        covered.update(set(declarations)&newnames)
        original=[r for r in old['material_claims'] if key in r['source_unit_keys']];pending=[r for r in original if r['status']=='pending']
        assert len(pending)==1 and pending[0]['source_unit_keys']==[key];removedids.add(pending[0]['id'])
        review_time=row.get('reviewed_at_utc',peer['reviewed_at_utc'])
        new={'id':key+'::independently-reviewed25-whole-literal','source_unit_keys':[key],
            'source':unit['source'],'locator':unit['locator'],'source_text':unit['source_text'],'source_text_sha256':unit['text_sha256'],
            'source_sha256':unit['source_sha256'],'statement_in_prose':unit['source_text'],'kind':'independently_reviewed_complete_mathematical_literal',
            'status':'proved','lean_declarations':declarations,'hypotheses':hypotheses,'correspondence':reason,'remaining_gaps':[],
            'source_review':{'file':rel(peerp),'sha256':sha(peerp),'reviewed_at_utc':review_time,'reviewer':peer['reviewer'],
            'reviewer_scope':'Exact original author-independent complete unit decision; entire prior peer row/body/time retained in interface.'}}
        candidate['material_claims']=[r for r in candidate['material_claims'] if r['id']!=pending[0]['id']];candidate['material_claims'].append(new)
        mappings.append({'source_unit_key':key,'entire_current52_inventory_record':unit,'entire_original_whole_literal_peer_row':row,
            'original_semantic_review':ref(peerp),'original_reviewed_at_utc':review_time,'original_full_peer_reviewed_at_utc':peer['reviewed_at_utc'],
            'entire_original_pending_clauses':pending,'retained_original_nonpending_clauses':[r for r in original if r['status']!='pending'],'new_candidate_claim':new})
assert len(mappedkeys)==len(removedids)==4 and len(newnames)==31 and len(newproofs)==2 and covered==newnames
candidate['proof_files']=sorted(set(candidate['proof_files']))
candidate['counts']['material_claim_statuses']=dict(Counter(r['status'] for r in candidate['material_claims']))
assert candidate['exercises']==old['exercises'] and candidate['surrounding_prose_reviews']==old['surrounding_prose_reviews'] and candidate['source_sha256']==old['source_sha256']
newids={r['new_candidate_claim']['id'] for r in mappings}
assert [r for r in old['material_claims'] if r['id'] not in removedids]==[r for r in candidate['material_claims'] if r['id'] not in newids]
assert sum(r['status']=='proved' for r in old['material_claims'])==1100
assert physical(old)=={'total':1756,'whole_proved':768,'nonformal':524,'whole_pending':464}
assert physical(candidate)=={'total':1756,'whole_proved':772,'nonformal':524,'whole_pending':460}
candidate['current25_owner_identity']={'inventory':ref(INV),'original24_ledger':ref(HELD),'original24_selection':ref(SELECTION),
    'actual_passed24_aggregate':ref(AUDIT),'unchanged_entire_foundation_source_records':1756,'unchanged_entire_foundation_exercise_records':119,
    'scope':'Isolated future25 current52 identity only; installed24 owners, selected/frozen24 sources and all earlier semantic bodies/times held exact.'}
candidate['current25_material_mapping']={'interface_binding':rel(INTERFACE),'whole_material_units':4,'removed_prior_pending_claims':4,
    'new_public_exports':31,'new_proof_sources':2,'already_selected_referenced_declaration_sources':referenced_selected,
    'physical_before':physical(old),'physical_after':physical(candidate),
    'scope':'Four exact author-independent original whole-unit decisions normalized with their entire original row/body/time retained; no semantic replacement or installed24 mutation.'}
candidate['limits'].append('Future25 isolated source52 candidate adds4 independently approved complete Foundation material units using2 genuine paired canonical source files/31 exports. All119 complete exercise bodies,1100 prior proved atoms and all original semantic bodies/hypotheses/times remain exact. Remaining460 physical units still require mathematical work; no aggregate25 or live-owner installation claim.')
write(CAND,candidate);guard()
interface={'status':'exact_original_four_complete_semantic_decisions_and_times_bound_to_isolated_candidate25',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_ledger':ref(CAND),'held_original24_ledger':ref(HELD),'current_inventory':ref(INV),
    'material_units':mappings,'proof_packets':packets,'all_original_TMP_byte_aliases':allaliases,'referenced_existing_selected24_proof_sources':referenced_selected,
    'all1756_units_and119_exercises_equal_source48_to52':True,'all_original1100_proved_atoms_and_semantic_bodies_times_exact':True,
    'physical_before':physical(old),'physical_after':physical(candidate),'coverage_complete':False}
write(INTERFACE,interface)
additional={rel(PACK):sha(PACK),rel(INTERFACE):sha(INTERFACE),rel(HELD):sha(HELD),**semanticrefs,**actualrefs,**readyrefs}
for r in allaliases.values():additional[r['file']]=r['sha256']
for n in ['prepare_foundations25_grid_and_calculus_originals_v1.py','run_foundations25_grid_and_calculus_canonical_pairs_v1.py','run_foundations25_grid_and_calculus_measured_step_v1.py']:
    p=ROOT/'book/coverage/checks'/n;additional[rel(p)]=sha(p)
for stem in ['prepare','pairs']:
    p=PACK.parent/f'two-source31-export-{stem}-actual-execution-v1.json';a=read(p)
    assert a['actual_exit_code']==0 and a['helper_sha256_before']==a['helper_sha256_after']
    lp=ROOT/a['log'];assert sha(lp)==a['log_sha256'];additional.update({rel(p):sha(p),rel(lp):sha(lp)})
draft={'schema_version':1,'status':'isolated_actual_paired_two_source31_export_four_whole_literal_candidate25_pending_independent_final_mechanics_and_canonical_binding',
    'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'base_selection':rel(SELECTION),'base_selection_sha256':SEL_SHA,
    'actual_passing_baseline_audit':rel(AUDIT),'actual_passing_baseline_audit_sha256':sha(AUDIT),'proof_files':newproofs,
    'new_proof_sources_for_checkpoint25':sorted(newproofs),'new_proof_file_count':2,'new_theorem_or_lemma_count':31,
    'mapped_ledger':rel(CAND),'mapped_ledger_sha256':sha(CAND),'held24_ledger':rel(HELD),'held24_ledger_sha256':sha(HELD),
    'working24_ledger':'book/coverage/foundations.json','working24_ledger_sha256':OLD_SHA,'source_sha256':candidate['source_sha256'],
    'current_inventory':rel(INV),'current_inventory_sha256':INV_SHA,'current_owner_builder':rel(Path(__file__)),'current_owner_builder_sha256':sha(Path(__file__)),
    'exact_source_reviews_sha256':semanticrefs,'actual_canonical_execution_records_sha256':actualrefs,'canonical_readiness_sha256':readyrefs,
    'material25_exact_interface_binding':rel(INTERFACE),'material25_exact_interface_binding_sha256':sha(INTERFACE),
    'new_material_dispositions':{'exact_current_rows':4,'whole_proved':4,'nonformal':0,'whole_pending':0,'previous_pending_claims_removed':4},
    'exercise_counts':candidate['counts']['exercise_statuses'],'material_counts':physical(candidate),'additional_frozen_inputs':additional,
    'original_semantic_reviews_body_and_time_retained':True,'independent_final_candidate_mapping_peer_pending':True,
    'independent_canonical_binding_peer_pending':True,'actual_builder_record_pending':True,'coverage_complete':False,
    'scope':'Isolated Foundation25 exact four whole material literals only;119 exercises/1100 old proved atoms retained, two genuine canonical paired sources/31 exports. No installed24 owner, current52 book, inventory or frozen24 change; no aggregate25 or live selection claim.'}
write(DRAFT,draft);guard()
integrity={'status':'passed_isolated_candidate_preserves_all_prior24_bodies_and_frozen_sources','checked_at_utc':datetime.now(timezone.utc).isoformat(),
    'held24_ledger':ref(HELD),'candidate':ref(CAND),'interface':ref(INTERFACE),'draft_offer':ref(DRAFT),
    'all1144_selected24_sources_and_frozen_copies_exact':True,'all31_current52_assets_and_frozen_copies_exact':True,
    'five_installed24_owner_sha256':owners,'all119_exercise_bodies_and1100_prior_proved_atoms_exact':True,
    'all1756_entire_foundation_source_records_equal48_to52':True,'removed_pending_claim_ids':sorted(removedids),'coverage_complete':False}
write(INTEGRITY,integrity);guard()
print(json.dumps({'status':'passed','candidate':ref(CAND),'interface':ref(INTERFACE),'draft_offer':ref(DRAFT),'integrity':ref(INTEGRITY),
                  'new_sources':2,'new_exports':31,'whole_units':4,'physical_after':physical(candidate)}))
