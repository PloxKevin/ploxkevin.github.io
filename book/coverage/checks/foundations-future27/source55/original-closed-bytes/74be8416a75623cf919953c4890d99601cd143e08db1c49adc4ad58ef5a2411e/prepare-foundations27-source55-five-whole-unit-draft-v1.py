from pathlib import Path
from datetime import datetime, timezone
from collections import Counter
import copy, hashlib, json, re
R=Path('/home/oxrexkevin/SafetyBased')
B=Path('/tmp/foundations27-source55-three-source43-five-whole-unit-draft-v1')
assert not B.exists()
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
REF=lambda p:{'file':str(p),'sha256':H(p)}
def write(p,d):
    with p.open('x') as f: json.dump(d,f,indent=2);f.write('\n')
BASE=R/'book/coverage/foundations.json'
INV=R/'book/coverage/inventory-after-correction55.json'
assert H(BASE)=='60b1ebaa5d44b3e371466d89cc9af68572ccdc069127504940a5c6c7ecd48b3a'
assert H(INV)==H(R/'book/coverage/inventory.json')=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
old=J(BASE);inv=J(INV);oldinv=J(R/'book/coverage/inventory-after-correction53.json')
units={u['key']:u for u in inv['material_source_units'] if u['source'] in old['scope_pages']}
exs={e['key']:e for e in inv['exercises'] if e['source'] in old['scope_pages']}
u53={u['key']:u for u in oldinv['material_source_units']};e53={e['key']:e for e in oldinv['exercises']}
assert len(units)==1756 and len(exs)==119
assert all(u==u53[k] for k,u in units.items()) and all(e==e53[k] for k,e in exs.items())
selection=J(R/'reports/full-coverage/checkpoint-26-selection.json')
binding=J(R/'book/coverage/checks/root-owner26-reviewed-candidate-bindings-v1.json')
application=J(R/'reports/full-coverage/source54-55-corrections-application-v1.json')
assert application['coverage_complete'] is False
assets={**binding['exact_current53_safelearning_assets_sha256'],**{x['source_after']['file']:x['source_after']['sha256'] for x in application['applications']}}
owners=J('/tmp/root-tmp-lean27-runner-independent-foundations-full-code-review-v3.json')['installed26_owners_sha256']
protected={**{f:x['sha256'] for f,x in selection['proof_files'].items()},**assets,**owners,
 'book/coverage/inventory.json':H(INV),'book/coverage/inventory-after-correction55.json':H(INV),
 'book/coverage/material-corrections.json':H(R/'book/coverage/material-corrections.json')}
assert len(selection['proof_files'])==1167 and len(assets)==31 and len(owners)==5
def guard():
    for f,h in protected.items():assert H(R/f)==h,f
guard()
peers=[
 Path('/tmp/foundations-balanced-sensor27-three-literals-independent-modules-full-source-review-v1.json'),
 Path('/tmp/foundations-balanced-sensor-spectral27-independent-modules-whole-source-review-v1.json'),
 Path('/tmp/foundations-matrix-residual17-independent-modules-whole-source-review27-v1.json')]
peerhashes=['05f83b5c0f50fe2e570bee24f02512a759e337200f115edc7593ff9508134492',
 '4c5f053a3e7997b39cb90f192d2e2fb87bc7e590c75d2a0fa8b5f347829d578c',
 'a2ba4024c7b8e6dcedfe813b692608d54a1c643f39e820e35471c4f3e13187d7']
sources=[Path('/tmp/foundations-balanced-sensor27-trial2.lean'),
 Path('/tmp/foundations-balanced-sensor-spectral27-trial2.lean'),Path('/tmp/foundations-matrix-residual-bridge27-trial2.lean')]
targetnames=['CompleteFoundationsBalancedSensorReconstruction27','CompleteFoundationsBalancedSensorSpectral27','CompleteFoundationsMatrixResidualOrthogonality27']
trials=[Path('/tmp/foundations-balanced-sensor27-trial2.json'),Path('/tmp/foundations-balanced-sensor-spectral27-trial2.json'),Path('/tmp/foundations-matrix-residual-bridge27-trial2.json')]
B.mkdir();A=B/'original-byte-aliases';A.mkdir()
aliases={};requested=[]
def collect(x):
    if isinstance(x,list):
        for y in x:collect(y)
    elif isinstance(x,dict):
        if type(x.get('file')) is str and re.fullmatch('[0-9a-f]{64}',str(x.get('sha256',''))):requested.append((x['file'],x['sha256']))
        for k,v in x.items():
            if type(k) is str and type(v) is str and re.fullmatch('[0-9a-f]{64}',v) and ('/' in k or k.endswith(('.py','.json','.log','.lean'))):requested.append((k,v))
            elif isinstance(v,(dict,list)):collect(v)
def resolve(f,h):
    p=Path(f);p=p if p.is_absolute() else R/p
    if p.is_file() and H(p)==h:return p
    if not Path(f).is_absolute():
        q=R/'reports/full-coverage/source-history/approved-mpc-conformal-corrections54-55-20261011/source53-original-root'/f
        if q.is_file() and H(q)==h:return q
    raise AssertionError(('no exact original byte source',f,h))
def archive(f,h):
    key=f+'::'+h
    if key in aliases:return aliases[key]['immutable_byte_copy']
    p=resolve(f,h);q=A/(h+'-'+Path(f).name)
    if not q.exists():
        with q.open('xb') as stream:stream.write(p.read_bytes())
    assert H(q)==h
    aliases[key]={'original_path':f,'original_sha256':h,'actual_byte_copy_source':str(p),'immutable_byte_copy':REF(q)}
    return REF(q)
candidate=copy.deepcopy(old);maps=[];packets=[];planned={};removed=set();newids=set();allnames=set()
for peer,expected,source,target,trial,count in zip(peers,peerhashes,sources,targetnames,trials,[16,10,17]):
    assert H(peer)==expected
    sem=J(peer);assert sem['errors']==[]
    assert sem['source']==REF(source)
    a=J(trial);assert type(a['actual_exit_code']) is int and a['actual_exit_code']==0
    assert a['actual_runner_exit_code']==0 and a['protection_errors']==[]
    assert a['actual_command']==['lake','env','lean',str(source)] and a['actual_workdir']==str(R/'verification/lean')
    assert a['source_sha256_before']==a['source_sha256_after']==H(source)==H(Path(a['source_snapshot']))
    assert H(Path(a['raw_log']))==a['raw_log_sha256']
    text=source.read_text();names=[];ns=None
    for line in text.splitlines():
        if line.startswith('namespace '):ns=line.split()[1]
        if line.startswith('theorem '):names.append(ns+'.'+line.split()[1])
    assert len(names)==count and not (set(names)&allnames)
    if 'all_public_declarations' in sem:assert names==sem['all_public_declarations']
    assert not re.search(r'\b(sorry|admit|axiom)\b',text)
    allnames.update(names)
    collect(sem);collect(a);requested.extend([(str(peer),expected),(str(source),H(source)),(str(trial),H(trial)),(a['source_snapshot'],a['source_snapshot_sha256']),(a['raw_log'],a['raw_log_sha256'])])
    desired='verification/lean/SafeLearning/'+target+'.lean'
    assert desired not in selection['proof_files'] and not (R/desired).exists()
    planned[desired]={'source_sha256':H(source),'exact_original_tmp_source':REF(source),'entire_source_bytes':text,
      'public_theorem_count':count,'all_public_declarations':names,
      'original_full_source_semantic_peer':REF(peer),'actual_original_tmp_standalone':REF(trial),
      'canonical_source_installation_executed':False,'canonical_standalone_executed':False,'named_build_executed':False,
      'canonical_pair_plan':[{'kind':'standalone','command':['lake','env','lean','SafeLearning/'+target+'.lean']},
        {'kind':'named','command':['lake','build','SafeLearning.'+target]}],
      'actual_workdir':str(R/'verification/lean'),'namespace_or_body_changes_planned':False}
    packets.append({'planned_canonical_source':desired,'original_tmp_source':REF(source),
      'original_semantic_review':REF(peer),'entire_original_semantic_body_and_time':sem,
      'entire_genuine_tmp_standalone_body_and_time':a,'public_theorem_count':count})
    for unit in sem['material_units']:
        key=unit['source_unit_key'];record=unit['entire_inventory_record']
        assert record==units[key] and unit['whole_literal_approved'] is True and unit['missing_clauses']==[]
        prior=[x for x in old['material_claims'] if key in x['source_unit_keys']]
        pending=[x for x in prior if x['status']=='pending']
        assert len(pending)==1 and pending[0]['source_unit_keys']==[key]
        removed.add(pending[0]['id'])
        hyps=unit['hypotheses'];hyps=hyps if isinstance(hyps,list) else [hyps]
        row={'id':key+'::independently-reviewed27-whole-literal-draft','source_unit_keys':[key],
          'source':record['source'],'locator':record['locator'],'source_text':record['source_text'],
          'source_text_sha256':record['text_sha256'],'source_sha256':record['source_sha256'],
          'statement_in_prose':record['source_text'],'kind':'independently_reviewed_complete_mathematical_literal',
          'status':'proved','lean_declarations':unit['lean_declarations'],'hypotheses':hyps,
          'correspondence':unit['reason'],'remaining_gaps':[],
          'source_review':{**REF(peer),'reviewed_at_utc':sem['reviewed_at_utc'],'reviewer':sem['reviewer'],
            'scope':'Exact original whole-literal decision/body/time. TMP semantic mapping draft; canonical standalone/named pairs are not executed.'}}
        newids.add(row['id']);candidate['material_claims']=[x for x in candidate['material_claims'] if x['id']!=pending[0]['id']];candidate['material_claims'].append(row)
        maps.append({'source_unit_key':key,'entire_current55_inventory_record':record,
          'entire_original_whole_literal_peer_row':unit,'original_semantic_review':REF(peer),
          'original_reviewed_at_utc':sem['reviewed_at_utc'],'entire_original_pending_rows':pending,
          'retained_original_nonpending_rows':[x for x in prior if x['status']!='pending'],'new_candidate_claim':row})
assert len(allnames)==43 and len(planned)==3 and len(maps)==len(removed)==5
assert {x['source_unit_key'] for x in maps}=={'primer-linalg.html::node-'+str(k) for k in (1264,1266,1268,1269,1289)}
assert candidate['exercises']==old['exercises'] and len(candidate['exercises'])==119
assert candidate['proof_files']==old['proof_files'] and candidate['proof_sha256']==old['proof_sha256']
assert candidate['source_sha256']==old['source_sha256'] and candidate['surrounding_prose_reviews']==old['surrounding_prose_reviews']
assert [x for x in old['material_claims'] if x['id'] not in removed]==[x for x in candidate['material_claims'] if x['id'] not in newids]
candidate['counts']['material_claim_statuses']=dict(Counter(x['status'] for x in candidate['material_claims']))
candidate['current55_owner_identity']={'inventory':REF(INV),'original_installed26_ledger':REF(BASE),
  'all1756_entire_owned_material_records_equal53_to55':True,'all119_entire_owned_exercise_records_equal53_to55':True,
  'scope':'Isolated TMP current55 identity only; no installed owner identity or global coverage assertion.'}
candidate['current27_material_mapping_draft']={'whole_units':5,'new_source_count':3,'new_public_exports':43,
  'planned_proof_files':planned,'canonical_paired_execution_pending':True,
  'remaining_execution_requirement':'Execute genuine exact-source canonical standalone and named commands for all3 sources, then obtain narrow canonical evidence binding and final candidate mechanics before an eligible reviewed offer.'}
candidate['limits'].append('TMP-only current55 semantic mapping draft adds5 independently approved whole units from3 genuinely passed TMP sources/43 public bodies. Canonical source installation and all6 canonical pair commands remain unexecuted; this is ineligible for live integration or production selection.')
for f,h in sorted(set(requested)):archive(f,h)
guard()
C=B/'foundations27-current55-five-whole-unit-candidate-draft-v1.json';write(C,candidate)
I=B/'foundations27-current55-five-whole-unit-interface-draft-v1.json'
write(I,{'status':'tmp_only_exact_original_whole_decisions_mapping_draft_canonical_execution_pending',
 'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_ledger':REF(C),'held_installed26_ledger':REF(BASE),
 'current_inventory':REF(INV),'material_units':maps,'proof_packets':packets,'exact_original_byte_aliases':aliases,
 'entire119_exercise_bodies_and_all_prior_positive_claims_retained':True,
 'all_owned_entire_records_unchanged53_to55':True,'canonical_pair_execution_count':0,'coverage_complete':False})
P=B/'foundations27-three-source43-canonical-pair-plan-unexecuted-v1.json'
write(P,{'status':'unexecuted_exact_source_canonical_pair_plan','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
 'source_count':3,'public_export_count':43,'planned_canonical_commands':6,'planned_sources':planned,
 'paired_execution_records':[],'current55_inventory':REF(INV),'held_installed26_ledger':REF(BASE),
 'canonical_or_named_execution_claimed':False,'scope':'Plan only; Root authorization/review and real protected execution required. No Root canonical/owner/source/PUB mutation performed.'})
D=B/'foundations27-current55-three-source43-five-whole-unit-readiness-draft-v1.json'
write(D,{'status':'tmp_only_semantic_mapping_draft_pending_canonical_pairs_and_independent_mechanics',
 'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_ledger':REF(C),'interface':REF(I),'canonical_pair_plan':REF(P),
 'installed26_baseline':REF(BASE),'current55_inventory':REF(INV),'source_count':3,'new_public_exports':43,
 'whole_material_unit_count':5,'original_whole_source_reviews':[REF(x) for x in peers],
 'original_byte_alias_count':len(aliases),'all119_exercises_unchanged':True,
 'original_positive_claim_count':sum(x['status']=='proved' for x in old['material_claims']),
 'new_positive_claim_count':sum(x['status']=='proved' for x in candidate['material_claims']),
 'original_pending_claim_count':sum(x['status']=='pending' for x in old['material_claims']),
 'new_pending_claim_count':sum(x['status']=='pending' for x in candidate['material_claims']),
 'canonical_pair_execution_count':0,'eligible_for_owner_integration_or_selection':False,
 'source53_global_is_historical_current55_identity_pending':True,'coverage_complete':False,
 'preserved_installed26_owner_sha256':owners,'prepared_by':REF(Path(__file__))})
guard();print(json.dumps({'status':'passed_tmp_only_draft_preparation','candidate':REF(C),'interface':REF(I),'plan':REF(P),'readiness':REF(D),'original_byte_alias_count':len(aliases),'canonical_pair_count':0}))
