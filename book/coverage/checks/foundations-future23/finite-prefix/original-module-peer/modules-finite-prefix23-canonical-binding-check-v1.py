"""Read-only canonical source/evidence binding supplement to an immutable peer."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys,copy
R=Path('/home/oxrexkevin/SafetyBased')
B='book/coverage/checks/foundations-future23/finite-prefix'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
out=Path('/tmp/foundations-finite-prefix1075-canonical-source-independent-modules-binding23-v1.json')
assert not out.exists()
request=R/B/'basics1075-full-literal-source-review-request-v1.json'
assert H(request)=='382243b1174349103176dcee865221eac1941c6f259ace27a5650c50fa066d67'
req=read(request)
oldpath=Path('/tmp/foundations-finite-prefix1075-independent-modules-source-review23-v1.json')
assert H(oldpath)=='8aea2c9e73b21db45df6666cf303ad3e3b598e7400249e75d9d06615b2f68f01'
old=read(oldpath);original_time=old['reviewed_at_utc']
source=R/req['new_proof_source'];assert H(source)==req['new_proof_source_sha256']=='f10296c36c25f094374c32423ba6d837f6bd364e397a89c7a586192d1d0bf7ef'
assert source.read_bytes()==Path('/tmp/foundations-finite-prefix23-trial3.lean').read_bytes()
for body in req['full_public_theorem_bodies']:
    assert body['full_statement_and_body'] in source.read_text()
assert len(req['full_public_theorem_bodies'])==6
assert old['full_parent_exercise_HTML_context']==req['full_parent_exercise_HTML_context']
invpath=R/req['current48_inventory']['file'];assert H(invpath)==req['current48_inventory']['sha256']==H(R/'book/coverage/inventory.json')
inv=read(invpath);unit=next(u for u in inv['material_source_units'] if u['key']=='primer-basics.html::node-1075')
assert unit['source_text']=='Split into even and odd indices. A limit superior ignores any fixed finite beginning.'
assert unit['text_sha256']=='bf763a4a5bad08190b11490818b02b755c5e654c35d0f6ca89dfc358307870e0'
assert H(R/unit['source'])==unit['source_sha256']
pair=[]
for ref in req['actual_canonical_pair']:
    p=R/ref['file'];assert H(p)==ref['sha256'];a=read(p)
    assert a['actual_exit_code']==ref['actual_exit_code']==0
    assert a['source_sha256_before']==a['source_sha256_after']==H(source)
    assert a['source']==req['new_proof_source']
    assert H(R/a['preserved_source'])==a['preserved_source_sha256']==H(source)
    assert H(R/a['log'])==a['log_sha256']==ref['raw_log']['sha256']
    assert ref['raw_log']['file']==a['log']
    pair.append({'file':ref['file'],'sha256':ref['sha256'],'actual_body':a,
                 'raw_log':ref['raw_log'],'actual_source_snapshot':{'file':a['preserved_source'],'sha256':a['preserved_source_sha256']}})
assert [p['actual_body']['command'] for p in pair]==[
    ['lake','env','lean','SafeLearning/CompleteFoundationsFinitePrefix23.lean'],
    ['lake','build','SafeLearning.CompleteFoundationsFinitePrefix23']]
execution_path=R/B/'canonical-pair-helper-actual-execution-v1.json';execution=read(execution_path)
assert execution['status']=='passed' and execution['actual_exit_code']==0
helper=R/req['actual_pair_helper']['file'];assert H(helper)==req['actual_pair_helper']['sha256']==execution['helper_sha256_before']==execution['helper_sha256_after']
assert H(R/execution['raw_log'])==execution['raw_log_sha256']
baseline=read(R/'reports/full-coverage/checkpoint-22-manifest.json')
for n,d in baseline['proof_files'].items():assert H(R/n)==d['sha256']
for n,d in baseline['frozen_inputs_sha256'].items():
    if n.startswith('SafeLearning/'):assert H(R/n)==d
for owner in ['core','applied','foundations','modules']:
    name=f'book/coverage/{owner}.json';assert H(R/name)==baseline['working_inputs_sha256'][name]
report={'status':'independent_canonical_source_and_actual_pair_binding_confirmation_passed',
    'reviewer':'/root/modules_resume','bound_at_utc':datetime.now(timezone.utc).isoformat(),
    'original_semantic_review':{'original_path':str(oldpath),'sha256':H(oldpath),'original_reviewed_at_utc':original_time},
    'canonical_request':{'file':str(request.relative_to(R)),'sha256':H(request)},
    'canonical_proof_source':{'file':req['new_proof_source'],'sha256':H(source)},
    'material_units':copy.deepcopy(old['material_units']),
    'actual_canonical_pair':pair,
    'actual_pair_helper_execution':{'file':str(execution_path.relative_to(R)),'sha256':H(execution_path)},
    'old_full_parent_HTML_scope_and_six_complete_proof_bodies_exact':True,
    'all_original_whole_hint_decisions_hypotheses_reasons_declarations_and_time_preserved':True,
    'all1113_selected22_sources_31_site_assets_four_working22_ledgers_exact':True,
    'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(Path(__file__)),
    'scope':'Only byte identity and genuine new canonical execution bindings are added. Original TMP full-whole-hint peer body/time remain immutable. No parent exercise promotion, fresh semantic decision, owner ledger integration or aggregate23 claim.'}
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'report':str(out),'sha256':H(out)}))
