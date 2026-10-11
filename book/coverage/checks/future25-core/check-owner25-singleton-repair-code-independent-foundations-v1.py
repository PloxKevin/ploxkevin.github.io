"""Read-only v3 singleton authorization/native schema fixtures. No main/dry/apply."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,re,types
ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/future25-core'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda n:{'file':n,'sha256':H(ROOT/n)}
I='book/coverage/checks/root_integrate_owner25_candidates_v3.py'
B='book/coverage/checks/prepare_root_owner25_bindings_v3.py'
assert H(ROOT/I)=='61e5f01dc3bc671d93e543caef716bc343933d0ba9f60a680d26b96e9e6b042d'
assert H(ROOT/B)=='9d510810736bfdc9e671c913d1720e97a85e6ae477b3a2c3388170b5cd371b5c'
def load(n,allowed):
    tree=ast.parse((ROOT/n).read_text())
    ns={'__file__':str(ROOT/n),'__name__':'independent_readonly_fixture'}
    nodes=[x for x in tree.body if isinstance(x,(ast.Import,ast.ImportFrom,ast.FunctionDef))or isinstance(x,ast.Assign)and all(isinstance(t,ast.Name)and t.id in allowed for t in x.targets)]
    exec(compile(ast.Module(body=nodes,type_ignores=[]),n,'exec'),ns)
    return ns,tree
ins,it=load(I,{'ROOT','REPORTS','OWNERS','AUXILIARIES','MUTABLE_DELIVERY_METADATA','BASE_MANIFEST','BASE_SHA','INVENTORY_SHA'})
bns,bt=load(B,{'ROOT','BASELINE','BASELINE_SHA','INVENTORY','INVENTORY_SHA','INTEGRATION','INTEGRATION_SHA','OWNERS','EXPECTED_SOURCES'})
vI=next(n for n in it.body if isinstance(n,ast.FunctionDef)and n.name=='validate_current_future_code_updates')
vB=next(n for n in bt.body if isinstance(n,ast.FunctionDef)and n.name=='validate_current_future_code_updates')
assert ast.dump(vI)==ast.dump(vB)
oldI='book/coverage/checks/root_integrate_owner25_candidates_v2.py'
oldB='book/coverage/checks/prepare_root_owner25_bindings_v2.py'
assert H(ROOT/oldI)=='cdb566bd8ef5d41d0c0856969c41c76f945ccf17c5bd153b83dbe59e6d9a3c8e'
assert H(ROOT/oldB)=='71f19be2c4a8f3a61966810e1453e90b3008243963c6e3164952b507a3ac9c9a'
# Every original function except build_binding is unchanged. The added shared
# function only validates the exact singleton metadata exception.
def defs(t):return {n.name:ast.dump(n)for n in t.body if isinstance(n,ast.FunctionDef)}
oldit=ast.parse((ROOT/oldI).read_text());oldbt=ast.parse((ROOT/oldB).read_text())
assert {k:v for k,v in defs(it).items()if k!='validate_current_future_code_updates'}==defs(oldit)
assert {k:v for k,v in defs(bt).items()if k not in {'validate_current_future_code_updates','build_binding'}}=={k:v for k,v in defs(oldbt).items()if k!='build_binding'}
oldloop=next(n for n in oldit.body if isinstance(n,ast.For)and ast.unparse(n.target)=='owner')
newloop=next(n for n in it.body if isinstance(n,ast.For)and ast.unparse(n.target)=='owner')
assert ast.dump(newloop)==ast.dump(oldloop)
# Protect original frozen maps; only the one validated expected working hash is
# replaced in the current guard before both pre-copy and post-copy checks.
code=(ROOT/I).read_text()
assert 'untouched_working[name] = digest'in code and code.count('for name, digest in untouched_working.items():')==2
assert 'retained_reference_sha256.update(future_code_validation["required_exact_provenance_sha256"])'in code
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-24-manifest.json').read_text())
auth_name='book/coverage/checks/root-owner25-authorized-future-code-updates-v1.json'
auth=json.loads((ROOT/auth_name).read_text())
assert H(ROOT/auth_name)=='65a0f1d21e0645663b290062112dec3cc071c9c1e018f2c359ab74f418faa052'
updates=auth['authorized_current_future_code_updates']
name=next(iter(updates))
expected_current={name:'53d47e49148a10f3dca53fff80514219e814764f557ae8f809c0d3dd28221fc6'}
fixtures=[]
def case(label,body,reject=False):
    try:body()
    except (AssertionError,KeyError,ValueError,TypeError,FileNotFoundError):
        assert reject,label
        fixtures.append({'fixture':label,'observed':'rejected'})
    else:
        assert not reject,label
        fixtures.append({'fixture':label,'observed':'accepted'})
for label,ns in [('integration',ins),('binding',bns)]:
    result=ns['validate_current_future_code_updates'](ROOT,manifest,updates,ref(auth_name))
    assert result['current_expected_sha256']==expected_current
    assert len(result['required_exact_provenance_sha256'])==17
    case(label+'_genuine_singleton_map_and_all17_original_provenance_refs',lambda:None)
    def mutated(edit):
        u=copy.deepcopy(updates);edit(u)
        return ns['validate_current_future_code_updates'](ROOT,manifest,u,ref(auth_name))
    for label2,edit in [
        ('empty_map',lambda u:u.clear()),
        ('extra_path',lambda u:u.update({'book/coverage/checks/not_authorized.py':copy.deepcopy(u[name])})),
        ('selected_lean_path',lambda u:u.update({'verification/lean/SafeLearning/BookApplications.lean':u.pop(name)})),
        ('absolute_path',lambda u:u.update({'/tmp/not_authorized.py':u.pop(name)})),
        ('wrong_old_hash',lambda u:u[name].update(old_working_sha256='0'*64)),
        ('wrong_current_hash',lambda u:u[name].update(current_sha256='0'*64)),
        ('extra_row_field',lambda u:u[name].update(inferred=True)),
        ('wrong_frozen_path',lambda u:u[name]['original_frozen_input'].update(file=name)),
        ('wrong_frozen_hash',lambda u:u[name]['original_frozen_input'].update(sha256=u[name]['current_sha256'])),
        ('wrong_peer_digest',lambda u:u[name]['independent_delta_peer'].update(sha256='0'*64)),
        ('wrong_wrapper_digest',lambda u:u[name]['actual_first_execution'].update(sha256='0'*64)),
        ('wrong_raw_digest',lambda u:u[name]['raw_log'].update(sha256='0'*64)),
        ('wrong_readiness_digest',lambda u:u[name]['closed_readiness'].update(sha256='0'*64)),
    ]:case(label+'_reject_'+label2,lambda edit=edit:mutated(edit),True)
    # These synthetic decoder fixtures keep real files unchanged. They exercise
    # field-level guards beyond the independently tested actual byte hash gate;
    # no synthetic execution or modified data is written or represented as real.
    realjson=ns['json']
    outer=json.loads((ROOT/updates[name]['actual_first_execution']['file']).read_text())
    def altered_native(edit):
        def decode(s):
            d=realjson.loads(s)
            if d==outer:d=copy.deepcopy(d);edit(d)
            return d
        ns['json']=types.SimpleNamespace(loads=decode)
        try:return ns['validate_current_future_code_updates'](ROOT,manifest,updates,ref(auth_name))
        finally:ns['json']=realjson
    for label2,edit in [
        ('boolean_exit',lambda d:d.update(actual_exit_code=False)),
        ('conflicting_exit',lambda d:d.update(exit_code=1)),
        ('nonzero_exit',lambda d:d.update(actual_exit_code=1)),
        ('conflicting_command',lambda d:d.update(command=['python3','wrong.py'])),
        ('wrong_cwd',lambda d:d.update(actual_workdir='/tmp')),
        ('helper_before_after_conflict',lambda d:d['helper_sha256_after'].update({name:'0'*64})),
        ('wrong_selection',lambda d:d.update(selection_sha256='0'*64)),
        ('pre_freeze_execution',lambda d:d.update(started_at_utc='2026-10-10T00:00:00+00:00')),
        ('raw_alias_conflict',lambda d:d.update(raw_log_sha256='0'*64))
    ]:case(label+'_reject_explicit_synthetic_native_'+label2,lambda edit=edit:altered_native(edit),True)
# All actual native owners/semantics/compiler records stay identical to the
# independently reviewed original binding. Only prospective new helper/peer and
# exact singleton metadata fields differ; missing v3 code gate is explicit fixture.
original_binding_name='book/coverage/checks/root-owner25-reviewed-candidate-bindings-v1.json'
original=json.loads((ROOT/original_binding_name).read_text())
config=json.loads((ROOT/'book/coverage/checks/root-owner25-binding-preparation-inputs-v1.json').read_text())
config['preparation_helper']=ref(B)
config['authorized_current_future_code_updates']=updates
config['current_future_code_update_authorization']=ref(auth_name)
synthetic_peer={'file':'book/coverage/checks/future25-core/explicit_synthetic_v3_code_fixture_peer.json','sha256':'f'*64}
config['independent_integration_helper_review']=synthetic_peer
realchecked=bns['checked']
bns['checked']=lambda r:{'status':'explicit_synthetic_code_fixture_passed','errors':[],'helper_sha256':H(ROOT/I)}if r==synthetic_peer else realchecked(r)
prospective=bns['build_binding'](config,'book/coverage/checks/root-owner25-binding-preparation-inputs-v1.json')
assert prospective['owners']==original['owners']
assert prospective['authorized_current_future_code_updates']==updates
assert prospective['current_future_code_update_authorization']==ref(auth_name)
assert prospective['authorized_current_future_code_update_reference_sha256']==result['required_exact_provenance_sha256']
assert prospective['new_proof_sources']==12 and prospective['original_canonical_execution_records']==24
case('read_only_current_native_four_owner24pair_binding_v3_reconstructs_original_owner_bodies_exact',lambda:None)
held={n:manifest['working_inputs_sha256'][n]for n in list(ins['OWNERS'].values())+list(ins['AUXILIARIES'])}
for n,h in held.items():assert H(ROOT/n)==h
for n,p in manifest['proof_files'].items():assert H(ROOT/n)==p['sha256']
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')}
for n,h in assets.items():assert H(ROOT/n)==h
old_peer_name='book/coverage/checks/future25-core/owner25-integration-and-binding-helpers-independent-foundations-code-review-v1.json'
old_peer=json.loads((ROOT/old_peer_name).read_text())
assert H(ROOT/old_peer_name)=='a01c88f5f7b9b3aac425e00f1a51be4ece8455d9388fa4c4a0fccc37d018e4b2'
failed='reports/full-coverage/owner25-integration-dry-execution-v1.json'
failure=json.loads((ROOT/failed).read_text())
assert type(failure['actual_exit_code'])is int and failure['actual_exit_code']==1
assert H(ROOT/failure['log'])==failure['log_sha256']
report={'status':'independent_owner25_singleton_authorization_integrator_and_binding_v3_full_delta_native_and_reject_fixtures_passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; v3 helper author Modules','helper_sha256':H(ROOT/I),'helpers_sha256':{I:H(ROOT/I),B:H(ROOT/B)},'root_exact_singleton_authorization':ref(auth_name),'identical_validator_functions_in_both_helpers':True,'all_original_integrator_functions_and_owner_loop_unchanged':True,'all_other_binding_functions_unchanged':True,'fixtures':fixtures,'fixture_count':len(fixtures),'explicit_synthetic_fixture_scope':'Only in-memory mutated maps/decoder objects and the still-absent v3 integration code-peer gate are synthetic. All actual authorization/provenance/owners/24 compiler records remain real and byte-exact; no production input/result is written and no integration is run.','original_v2_code_peer_body_and_time_unchanged':old_peer,'original_v2_actual_dry_failure_preserved':ref(failed),'entire_original_dry_failure_record_and_time':failure,'original_binding_v1':ref(original_binding_name),'original_native_four_owner_semantic_and_pair_bodies_retained':True,'actual_current_proof_source_count':1144,'all31_current52_assets_and_five_held24_owner_hashes_exact':True,'required_exact_singleton_provenance_sha256':result['required_exact_provenance_sha256'],'coverage_complete':False,'scope':'Code/native-schema review only. Exactly one reviewed old frozen future-code draft may use its pinned genuine executed current hash in the current working guard; its original frozen bytes remain fully checked. Every other immutable working input, original candidate/semantic/compiler body/time and selected24 proof remains unchanged. A fresh genuine binding2, Root dry/apply, global integrity and live output reviews are still required.'}
out=BASE/'owner25-singleton-repair-independent-foundations-observations-v1.json'
assert not out.exists()
out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':report['status'],'observation':ref(str(out.relative_to(ROOT))),'fixtures':len(fixtures),'sources':12,'original_actual_pairs':24}))
