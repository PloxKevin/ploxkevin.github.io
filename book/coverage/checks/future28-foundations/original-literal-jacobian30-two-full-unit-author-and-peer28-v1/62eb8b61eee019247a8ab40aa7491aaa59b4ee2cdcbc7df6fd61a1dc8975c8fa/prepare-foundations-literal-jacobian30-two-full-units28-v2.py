from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=Path('/tmp/foundations-literal-jacobian30-two-full-units28-v2')
assert not BASE.exists();BASE.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
def read(p):return json.loads(Path(p).read_bytes())
oldp=Path('/tmp/foundations-literal-jacobian27-two-full-units28-v1/foundations-literal-jacobian27-two-full-units28-v1.json');assert sha(oldp)=='99dde84d022ebd69785dcea3c537c176e0450acc887733bbbc7267da796d4529';old=read(oldp)
peerp=Path('/tmp/foundations-jacobian27-independent-modules-review28-v1.json');assert sha(peerp)=='e1144d375674ad6c1a173bcae24448a3ecd1ee21416b2e9f4589e8d5165eec62';peer=read(peerp)
assert peer['errors']==[] and all(u['whole_approved']is False and len(u['remaining_gaps'])==1 for u in peer['individual_unit_decisions'])
source=Path('/tmp/CompleteFoundationsLiteralJacobian28-draft-v7.lean');assert sha(source)=='0d1aa1bb7667f67518620f18870c785dd36fb0eacffef60d14b386b910a5db61';s=source.read_text();end='end SafeLearning.CompleteFoundationsLiteralJacobian28\n';prefix=old['entire_source'].removesuffix(end);assert old['entire_source']==prefix+end and s.startswith(prefix)
assert not re.search(r'\b(sorry|admit|axiom)\b',s)
sel=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json');assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256'];owners={r['destination']:r['candidate']['sha256']for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']};held={n:r['sha256']for n,r in sel['proof_files'].items()};held.update(assets);held.update(owners);held.update({'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'})
def guard():
 for n,h in held.items():assert sha(ROOT/n)==h,n
assert len(sel['proof_files'])==1175 and len(assets)==31 and len(owners)==5
started=datetime.now(timezone.utc).isoformat();guard();decls=[];namespace=None
for line in s.splitlines():
 if line.startswith('namespace '):namespace=line.split()[1]
 if line.startswith('theorem '):decls.append(namespace+'.'+line.split()[1])
assert len(decls)==30 and decls[:27]==old['public_theorem_names']
p=Path('/tmp/foundations-literal-jacobian30-28-trial7.json');a=read(p);raw=Path(a['raw_log']);snapshot=Path(a['source_snapshot'])
assert a['actual_exit_code']==a['actual_runner_exit_code']==0 and a['protection_errors']==[] and a['source_unchanged']is True
assert sha(raw)==a['raw_log_sha256']and raw.read_bytes()==b''
assert sha(source)==sha(snapshot)==a['source_snapshot_sha256']==a['source_sha256_before']==a['source_sha256_after']
assert a['actual_command']==['lake','env','lean',str(source)]and a['actual_workdir']==str(ROOT/'verification/lean')
assert a['protected_selected27_proof_sources']==1175 and a['unchanged_current55_book_assets']==31 and a['unchanged_installed27_live_owners']==5 and a['installed27_owner_sha256']==owners
for n,h in a['pinned_installed27_provenance_sha256'].items():assert sha(ROOT/n)==h,n
aliases=dict(old['original_closed_byte_aliases'])
for n,r in aliases.items():assert sha(n)==r['sha256']==sha(r['file']),n
peeractual=Path('/tmp/foundations-jacobian27-independent-modules-review28-checker-actual-v1.json');pa=read(peeractual);assert pa['actual_exit_code']==0
files=[source,p,raw,snapshot,oldp,peerp,peeractual,Path('/tmp/foundations-jacobian27-independent-modules-review28-checker-actual-v1.log'),Path('/tmp/review-foundations-jacobian27-independent-modules28-v1.py'),Path('/tmp/run-foundations-jacobian27-independent-modules-review28-v1.py')]
for f in files:
 h=sha(f);q=BASE/'original-closed-bytes'/h/f.name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,q);assert f.read_bytes()==q.read_bytes();aliases[str(f)]={'file':str(q),'sha256':h}
d=dict(old);d.update({'status':'actual_tmp_lean_passed_full_jacobian30_188_190_request_independent_whole_literal_review','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'started_at_utc':started,'source':ref(source),'entire_source':s,'public_theorem_count':30,'public_theorem_names':decls,'original_closed_byte_aliases':aliases,'exact_all_old27_definitions_and_proof_bodies_unchanged_prefix':True,'new_public_theorem_names':decls[27:],'new_definition':'actualPartialJacobian is the total array of scalar coordinate-slice deriv values, defined independently of Frechet differentiability; existence of derivatives is a separate hypothesis.','retained_original_jacobian27_author_request_body_time_reference':{'ref':ref(oldp),'original_prepared_at_utc':old['prepared_at_utc'],'entire_body_and_time_preserved_by_exact_original_reference':True},'retained_original_jacobian27_semantic_pending_peer_body_time_reference':{'ref':ref(peerp),'actual_reader_execution':ref(peeractual),'original_started_at_utc':peer['started_at_utc'],'original_reviewed_at_utc':peer['reviewed_at_utc'],'original_status':peer['status'],'original_individual_unit_decisions':peer['individual_unit_decisions'],'entire_body_and_time_preserved_by_exact_original_reference':True,'reader_failed':False,'scope':'Original actual0 reader intentionally kept both whole units pending for the literal partial-array definition bridge. Its measured semantic decision remains unchanged.'},'remaining_independent_review_obligation':'Read all30 full bodies/definitions and both whole literals, compare the unchanged old27 prefix and new actual-partial-array definition plus three bridges, and explicitly approve/reject each entire literal. Genuine compilation/integrity does not itself establish source correspondence.','scope':'TMP full-unit author request only. Seven genuine compiler histories and the prior intentional semantic pending peer retained without retiming. Current55/installed27 owners, selection and canonical proofs unchanged. Prior histories are bounded exact references.'})
d['actual_trials_full_original_bodies_times_and_raw']=old['actual_trials_full_original_bodies_times_and_raw']+[{'record':ref(p),'entire_original_body_and_time':a,'raw_log':ref(raw),'entire_raw_log':'','source_snapshot':ref(snapshot),'entire_source_snapshot':snapshot.read_text(),'actual_emitted_warning_count':0}]
ns='SafeLearning.CompleteFoundationsLiteralJacobian28.'
d['all_literal_clause_correspondence']=list(old['all_literal_clause_correspondence'])
d['all_literal_clause_correspondence'][0]={'literal_clause':'Finite rectangular Jacobian definition as actual partial entries, including when only partials exist','lean_declarations':[ns+'actual_partial_entry_array_agrees_with_the_frechet_matrix_when_components_are_differentiable',ns+'actual_scalar_partial_jacobian_entries_are_the_true_coordinate_partials'],'definition':'actualPartialJacobian','correspondence':'The generic literal array is defined from genuine coordinate slice deriv; at component-differentiable points it equals the Frechet sourceJacobian. For a scalar output its entries are definitionally the actual coordinatePartial values. Existence of partials alone supplies no Frechet derivative.'}
d['all_literal_clause_correspondence'][6]['lean_declarations'].append(ns+'actual_printed_pitfall_has_the_zero_partial_jacobian_without_a_linear_approximation')
d['all_literal_clause_correspondence'][6]['correspondence']+=' The literal Fin1 actualPartialJacobian is explicitly zero at the origin while no first-order linear approximation exists.'
assert all(n in decls for row in d['all_literal_clause_correspondence']for n in row['lean_declarations'])
assert d['whole_material_units_approved']is False and d['canonical_or_named_execution_claimed']is False
guard();out=BASE/'foundations-literal-jacobian30-two-full-units28-v2.json'
with out.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'request':ref(out),'bytes':out.stat().st_size,'source':ref(source),'public_theorems':30,'original_alias_count':len(aliases),'trial_warning_counts':[t['actual_emitted_warning_count']for t in d['actual_trials_full_original_bodies_times_and_raw']],'prior_semantic_pending_reader_failed':False}))
