"""Author-independent read-only25 code/native-schema fixtures; no main/dry/apply/production binding."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future25-core'
I=ROOT/'book/coverage/checks/root_integrate_owner25_candidates_v2.py';B=ROOT/'book/coverage/checks/prepare_root_owner25_bindings_v2.py'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();ref=lambda p:{'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
read=lambda n:json.loads((ROOT/n).read_text())
assert H(I)=='cdb566bd8ef5d41d0c0856969c41c76f945ccf17c5bd153b83dbe59e6d9a3c8e'
assert H(B)=='71f19be2c4a8f3a61966810e1453e90b3008243963c6e3164952b507a3ac9c9a'
isrc=I.read_text();bsrc=B.read_text();it=ast.parse(isrc);bt=ast.parse(bsrc)
# Only definitions and fixed globals are executed, never either main/top-level integration.
def load(p,t,allowed):
 ns={'__file__':str(p),'__name__':'independent_code_fixture'}
 nodes=[n for n in t.body if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef))or isinstance(n,ast.Assign)and all(isinstance(x,ast.Name)and x.id in allowed for x in n.targets)]
 exec(compile(ast.Module(body=nodes,type_ignores=[]),str(p),'exec'),ns);return ns
ins=load(I,it,{'ROOT','REPORTS','OWNERS','AUXILIARIES','MUTABLE_DELIVERY_METADATA','BASE_MANIFEST','BASE_SHA','INVENTORY_SHA'})
bns=load(B,bt,{'ROOT','BASELINE','BASELINE_SHA','INVENTORY','INVENTORY_SHA','INTEGRATION','INTEGRATION_SHA','OWNERS','EXPECTED_SOURCES'})
original_i=ROOT/'book/coverage/checks/root_integrate_owner25_candidates_v1.py';original_b=ROOT/'book/coverage/checks/prepare_root_owner25_bindings_v1.py'
assert H(original_i)=='fca0f767652c079d280bf6112767f0b4bc9bcb7d09929f2c85b06c82c4e1a973'and H(original_b)=='9ee6b4ceaffc970d6ee42efa54870909ec930759d01d7b3917451b7d622a9d6a'
oldit=ast.parse(original_i.read_text());norm=copy.deepcopy(it)
norm.body=[n for n in norm.body if not isinstance(n,ast.FunctionDef)or n.name!='zero']
# Prove no scope delta except strict exit checking at the same four required sites.
def revert(nodes):
 out=[]
 for n in nodes:
  u=ast.unparse(n)
  if u=='zero(source52)':out.append(ast.parse('assert source52["actual_exit_code"] == source52_postwrite["actual_exit_code"] == 0').body[0])
  elif u=='zero(source52_postwrite)':continue
  elif u=='zero(actual_builder)':out.append(ast.parse('assert actual_builder["actual_exit_code"] == 0').body[0])
  elif u=='zero(execution)':
   out.extend(ast.parse('exits = [execution[field] for field in ["exit_code", "actual_exit_code"] if field in execution]\nassert exits and all(value == 0 for value in exits)').body)
  else:
   for k in ('body','orelse','finalbody'):
    v=getattr(n,k,None)
    if isinstance(v,list):setattr(n,k,revert(v))
   out.append(n)
 return out
norm.body=revert(norm.body);assert ast.dump(norm)==ast.dump(oldit),'Unrequested integration-v2 delta'
assert bsrc.replace('root_integrate_owner25_candidates_v2.py','root_integrate_owner25_candidates_v1.py').replace('cdb566bd8ef5d41d0c0856969c41c76f945ccf17c5bd153b83dbe59e6d9a3c8e','fca0f767652c079d280bf6112767f0b4bc9bcb7d09929f2c85b06c82c4e1a973')==original_b.read_text()
fixtures=[]
def case(name,body,reject=False):
 try:body()
 except (AssertionError,KeyError,ValueError,TypeError,FileNotFoundError):assert reject,name;fixtures.append({'fixture':name,'observed':'rejected'})
 else:assert not reject,name;fixtures.append({'fixture':name,'observed':'accepted'})
for n in ['/tmp/notcanonical','../outside']:
 case('integration_reject_unsafe_'+n,lambda n=n:ins['safe_path'](n),True);case('binding_reject_unsafe_'+n,lambda n=n:bns['safe'](n),True)
for label,ns in [('integration',ins),('binding',bns)]:
 case(label+'_equal_integer_exit_aliases',lambda ns=ns:ns['zero']({'actual_exit_code':0,'exit_code':0}))
 for n,record in [('boolean',{'actual_exit_code':False}),('float',{'exit_code':0.0}),('missing',{}),('nonzero',{'actual_exit_code':1}),('conflict',{'actual_exit_code':0,'exit_code':1})]:case(label+'_reject_exit_'+n,lambda ns=ns,record=record:ns['zero'](record),True)
manifest=read('reports/full-coverage/checkpoint-24-manifest.json');assert H(ROOT/'reports/full-coverage/checkpoint-24-manifest.json')==ins['BASE_SHA']
assert len(manifest['proof_files'])==1144 and len(manifest['frozen_inputs_sha256'])==40485
for n,row in manifest['proof_files'].items():assert H(ROOT/n)==row['sha256']
assets={n:d for n,d in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
for n,d in assets.items():assert H(ROOT/n)==d
held={n:manifest['working_inputs_sha256'][n]for n in list(ins['OWNERS'].values())+list(ins['AUXILIARIES'])}
for n,d in held.items():assert H(ROOT/n)==d
observation_name='book/coverage/checks/future25-core/checkpoint25-native-final-owner-binding-request-observation-v1.json'
observation=read(observation_name);config=copy.deepcopy(observation['production_binding_input_template_without_independent_helper_peer'])
config['preparation_helper']=ref(B)
fixture_peer={'file':'book/coverage/checks/future25-core/explicit-synthetic-code-fixture-peer.json','sha256':'f'*64}
config['independent_integration_helper_review']=fixture_peer
real_checked=bns['checked']
bns['checked']=lambda r:{'status':'explicit_synthetic_code_fixture_passed','errors':[],'helper_sha256':H(I)}if r==fixture_peer else real_checked(r)
# Read-only function call, with an explicitly synthetic missing code-peer object.
# The returned prospective object is kept only in memory, never a production input.
prospective=bns['build_binding'](config,observation_name)
assert prospective['new_proof_sources']==12 and prospective['original_canonical_execution_records']==24
assert set(prospective['owners'])==set(ins['OWNERS'])
assert set(prospective['exact_current52_safelearning_assets_sha256'])==set(assets)
assert all(prospective['exact_current52_safelearning_assets_sha256'][n]==d for n,d in assets.items())
case('read_only_binding_function_against_all_four_current_final_offers_with_explicit_synthetic_peer',lambda:None)
# Execute the literal integration owner-validation loop in memory against that
# prospective binding. All reference objects/byte hashes are genuine except the
# explicitly identified missing integration code-peer gate above.
ownerloop=next(n for n in it.body if isinstance(n,ast.For)and ast.unparse(n.target)=='owner')
env=dict(ins,binding=prospective,manifest=manifest,assets=assets,replacements=[],retained_reference_sha256={},seen_new_proofs={},held24_non_safelearning_source_sha256={})
exec(compile(ast.Module(body=[ownerloop],type_ignores=[]),str(I),'exec'),env)
assert len(env['replacements'])==5 and len(env['seen_new_proofs'])==12
raw_owner_paths=set(ins['OWNERS'].values())|ins['AUXILIARIES']
assert not(raw_owner_paths&set(env['retained_reference_sha256'])),'Retained original references must not falsely require obsolete working-owner SHA after exact-copy installation'
actual_pairs=[r for owner in prospective['owners'].values()for proof in owner['new_immutable_proof_sources'].values()for r in proof['actual_pair']];assert len(actual_pairs)==24
case('all12_real_canonical_sources_and24_native_integer0_pairs_pass_both_helpers',lambda:None)
# Exact isolated paired-record normalization fixtures, modifying dictionaries only.
first_owner=prospective['owners']['foundations'];source,proof=next(iter(first_owner['new_immutable_proof_sources'].items()));pair=proof['actual_pair'][0]
actual=real_checked({k:pair[k]for k in ['file','sha256']});original_proof=real_checked(config['offers']['foundations'])['proof_files'][source]
real_read=bns['read']
def pair_fixture(edit=None,evidence_edit=None):
 record=copy.deepcopy(actual);p=copy.deepcopy(original_proof)
 if edit:edit(record)
 if evidence_edit:evidence_edit(p['evidence_sha256'])
 bns['read']=lambda n:record if n==pair['file']else real_read(n)
 try:return bns['canonical_pair'](source,p)
 finally:bns['read']=real_read
case('canonical_pair_equal_command_aliases',lambda:pair_fixture(lambda r:r.update(command=r.get('command',r.get('actual_command')),actual_command=r.get('command',r.get('actual_command')))))
for name,edit in [('boolean_exit',lambda r:r.update(actual_exit_code=False)),('conflicting_exit',lambda r:r.update(exit_code=1)),('conflicting_command',lambda r:r.update(command=['false'])),('wrong_workdir',lambda r:r.update(actual_workdir='/tmp')),('changed_source_after',lambda r:r.update(source_sha256_after='0'*64)),('conflicting_rawlog',lambda r:r.update(log_sha256='0'*64,raw_log_sha256='1'*64)),('TMP_only_command',lambda r:r.update(actual_command=['lake','env','lean','/tmp/source.lean'],command=['lake','env','lean','/tmp/source.lean'])),('wrong_snapshot_hash',lambda r:r.update(source_snapshot_sha256='0'*64))]:case('canonical_pair_reject_'+name,lambda edit=edit:pair_fixture(edit),True)
case('canonical_pair_reject_missing_exact_rawlog_evidence',lambda:pair_fixture(evidence_edit=lambda e:[e.pop(n)for n in list(e)if n.endswith('.log')]),True)
# Semantic decisions/times are compared exactly, including a legitimately whole-
# pending status; status strings must not be rewritten to manufacture 'passed'.
semloop=next(n for n in ownerloop.body if isinstance(n,ast.For)and ast.unparse(n.iter)=="row['original_full_source_semantic_reviews']")
def semfixture(edit=None):
 body={'status':'original_components_approved_whole_pending','checked_at_utc':'original-time','errors':[]}
 r={'file':'fixture','sha256':'a'*64,'original_review_status':body['status'],'original_review_time':body['checked_at_utc']}
 if edit:edit(body,r)
 local={'row':{'original_full_source_semantic_reviews':[r]},'reference':lambda x:body,'retained_reference_sha256':{}}
 exec(compile(ast.Module(body=[semloop],type_ignores=[]),str(I),'exec'),local)
case('original_component_approved_whole_pending_status_is_preserved',lambda:semfixture())
case('reject_semantic_status_reinterpretation',lambda:semfixture(lambda b,r:r.update(original_review_status='passed')),True)
case('reject_semantic_time_redating',lambda:semfixture(lambda b,r:r.update(original_review_time='fresh-time')),True)
case('reject_semantic_errors',lambda:semfixture(lambda b,r:b.update(errors=['gap'])),True)
# Native body validation rejects altered candidate pointers and held-owner bytes.
def ownerfixture(edit):
 fixture=copy.deepcopy(prospective);edit(fixture)
 local=dict(ins,binding=fixture,manifest=manifest,assets=assets,replacements=[],retained_reference_sha256={},seen_new_proofs={},held24_non_safelearning_source_sha256={})
 exec(compile(ast.Module(body=[ownerloop],type_ignores=[]),str(I),'exec'),local)
case('reject_held_owner_digest_change',lambda:ownerfixture(lambda b:b['owners']['applied'].update(held24_ledger_sha256='0'*64)),True)
case('reject_false_ready_owner',lambda:ownerfixture(lambda b:b['owners']['core'].update(ready=False)),True)
case('reject_candidate_offer_pointer_mismatch',lambda:ownerfixture(lambda b:b['owners']['core'].update(offer_candidate_path_pointer=['inventory_sha256'])),True)
case('reject_candidate_peer_pointer_mismatch',lambda:ownerfixture(lambda b:b['owners']['foundations'].update(peer_candidate_sha256_pointer=['status'])),True)
case('reject_non_applied_companion',lambda:ownerfixture(lambda b:b['owners']['modules'].update(companion_candidates=[b['owners']['applied']['companion_candidates'][0]])),True)
# All immutable checks precede the only --apply archive/atomic-copy block.
apply=next(n for n in it.body if isinstance(n,ast.If)and ast.unparse(n.test)=='args.apply');applytext=ast.unparse(apply)
assert "original24_byte_copy"in applytext and "os.replace(temporary, original)"in applytext
assert "with preserved.open('xb')"in applytext and "with temporary.open('xb')"in applytext
assert 'verify_frozen_and_sources()'in applytext
assert 'for name, digest in retained_reference_sha256.items()'in applytext
assert 'for name, digest in held24_non_safelearning_source_sha256.items()'in applytext
assert 'allowed_destinations = set(OWNERS.values()) | AUXILIARIES'in isrc
assert 'assert not safe_path(report_name).exists()'in isrc
assert 'source52' in isrc and 'all40485_frozen24_inputs_exact'in isrc and 'all1144_selected24_root_source_hashes_exact'in isrc
assert 'with safe(destination).open(\'x\')'in bsrc and '--root-authorized-binding-preparation'in bsrc
assert not any(isinstance(n,ast.Call)and ast.unparse(n.func)=='build_binding'for n in bt.body if not isinstance(n,ast.FunctionDef))
for n,d in held.items():assert H(ROOT/n)==d
obs={'status':'passed_independent_owner25_integration_and_binding_helpers_code_and_focused_native_schema_fixtures','errors':[],'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':H(I),'helpers_sha256':{str(I.relative_to(ROOT)):H(I),str(B.relative_to(ROOT)):H(B)},'checker':ref(Path(__file__)),'original_unexecuted_v1_helpers':{str(original_i.relative_to(ROOT)):H(original_i),str(original_b.relative_to(ROOT)):H(original_b)},'baseline24_manifest':ref(ROOT/ins['BASE_MANIFEST']),'all1144_selected24_sources_rehashed':True,'all31_source52_assets_rehashed':True,'held24_working_owner_sha256':held,'current_final_offers':config['offers'],'original_native_author_observation':ref(ROOT/observation_name),'real_native_pair_records_tested':actual_pairs,'new_source_count':12,'actual_native_pair_record_count':24,'strict_exit_delta_is_only_integration_v1_to_v2_change':True,'binding_v2_only_pins_corrected_integration':True,'fixture_count':len(fixtures),'fixtures':fixtures,'full_read_scope':['four exact current52 candidate/offer/mapping-peer pointers and original semantic status/time/body-hash preservation','all12 genuine canonical sources,24 native standalone/named records, exact rawlogs/source before+after/cwd/commands/snapshots and historical TMP ineligibility','1144 selected24 proof and40485 immutable frozen-snapshot pre/post guard code; current52 inventory/source registry/all31 same-baseline assets','five explicit old24 raw-owner archives and exact reviewed atomic-copy destinations only','no sourceHTML/currentinventory/selectedproof mutation and fresh global25/selection/aggregate/site phases remain required'],'scope':'Code approval only. The exact read-only binding function and literal owner-validation loop were exercised in memory against all four actual final offers and all24 genuine compiler records; the not-yet-published integration helper peer was an explicitly synthetic test object. No production binding/input was written or approved, no main/dry/apply/archive/copy executed, no compiler rerun, no live owner/HTML/selection/freeze/publication mutation. Root requires the real closed independent helper peer, actual binding manifest and its separate independent output check before release.'}
out=BASE/'owner25-integration-and-binding-independent-foundations-observations-v1.json'
with out.open('x')as f:f.write(json.dumps(obs,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':obs['status'],'observations':ref(out),'fixtures':len(fixtures),'native_pairs':24}))
