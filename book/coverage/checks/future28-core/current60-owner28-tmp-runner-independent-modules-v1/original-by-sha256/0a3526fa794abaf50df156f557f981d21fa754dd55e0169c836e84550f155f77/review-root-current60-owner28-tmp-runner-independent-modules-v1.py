from pathlib import Path
from datetime import datetime,timezone
from types import SimpleNamespace
from unittest.mock import patch
import ast,hashlib,json,sys,copy
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');H=Path('/tmp/root_tmp_lean_current60_owner28_runner_v1.py');C=Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json');B=Path('/tmp/root-current60-owner28-tmp-runner-independent-modules-v1');assert not B.exists();B.mkdir();sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();ref=lambda p:{'file':str(p),'sha256':sha(p)}
assert sha(H)=='f9f9f273bfa7c0f22d78f75fed23d32af794f13d51f329ae06747d3dac691c1a';assert sha(C)=='35ac327b8d62c70dd9e0f83236716ee465d9b188cf656c58be97078b3eea5054'
text=H.read_text();tree=ast.parse(text);context=json.loads(C.read_bytes());assert context['status']=='actual_current60_owner28_verified_context_for_new_tmp_trials_only';assert context['coverage_complete']is False
selection=json.loads((R/context['selection']['file']).read_bytes());audit=json.loads((R/context['actual_audit']['file']).read_bytes());assert sha(R/context['selection']['file'])==context['selection']['sha256'];assert sha(R/context['actual_audit']['file'])==context['actual_audit']['sha256']
assert selection['proof_file_count']==len(selection['proof_files'])==1186 and selection['new_file_count']==11
proofs={n:v['sha256']for n,v in selection['proof_files'].items()};assert {n:context['held_current_source_sha256'][n]for n in proofs}==proofs
assert audit['status']=='passed'and audit['proof_file_count']==1186 and audit['theorem_count']==9896 and audit['proof_sha256']==proofs
assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9896
assert {d['name']for d in audit['declarations']}==set(audit['axiom_dependencies']);assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'};assert all(set(v)<=set(audit['allowed_standard_axioms'])for v in audit['axiom_dependencies'].values())
assert sum(x.get('evidence_mode')=='fresh_kernel_replay'for x in audit['checks'])==11;assert sum(x.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports'for x in audit['checks'])==1175
owners=context['owners_sha256'];assert set(owners)=={'book/coverage/'+n+'.json'for n in ['core','foundations','applied','applied-promotions','modules']};assert all(context['held_current_source_sha256'][n]==h for n,h in owners.items())
assets={n:h for n,h in context['held_current_source_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31;inv=json.loads((R/'book/coverage/inventory.json').read_bytes());assert inv['source_sha256']=={n:h for n,h in assets.items()if n.endswith('.html')}
assert len(json.loads((R/'book/coverage/material-corrections.json').read_bytes())['corrections'])==60
allpins={**context['pins_sha256'],**context['held_current_source_sha256']};assert len(context['pins_sha256'])==14 and len(context['held_current_source_sha256'])==1228
for n,h in allpins.items():
 p=R/n;assert not Path(n).is_absolute()and '..'not in Path(n).parts and p.resolve().is_relative_to(R)and not p.is_symlink()and sha(p)==h,n
working='verification/lean/SafeLearning.lean';frozen='reports/full-coverage/checkpoint-28/verification/lean/SafeLearning.lean';assert context['held_current_source_sha256'][working]!=context['held_current_source_sha256'][frozen]
assert audit['project_sha256'][working]==context['held_current_source_sha256'][frozen]
# Stop the exact original code before its first top-level guard()/snapshot/compiler operation.
cut=next(i for i,n in enumerate(tree.body)if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Name)and n.value.func.id=='guard')
prefix=ast.Module(body=tree.body[:cut],type_ignores=[])
assert not any(isinstance(n,ast.Call)and isinstance(n.func,ast.Attribute)and isinstance(n.func.value,ast.Name)and n.func.value.id=='subprocess'for n in ast.walk(prefix))
fixtures=[];counter=0
def case(label,source_text='namespace SyntheticPrefixOnly\ntheorem trivial_true : True := by trivial\nend SyntheticPrefixOnly\n',configure=None,mutation=None,expect=True,full=False,fake=None):
 global counter
 counter+=1;D=B/'synthetic_fixtures_no_lean_compiler'/f'{counter:02d}-{label}';D.mkdir(parents=True);s=D/'source.lean';r=D/'output.json';s.write_text(source_text);g={'__file__':str(H),'__name__':'independent_fixture_exec'};argv=[str(H),str(s),str(r)]
 t=copy.deepcopy(tree if full else prefix)
 if mutation is not None:
  c=copy.deepcopy(context);mutation(c);cp=D/'synthetic-context.json';cp.write_text(json.dumps(c,indent=2)+'\n')
  for n in t.body:
   if isinstance(n,ast.Assign)and any(isinstance(x,ast.Name)and x.id=='CONTEXT'for x in n.targets):n.value=ast.Call(func=ast.Name(id='Path',ctx=ast.Load()),args=[ast.Constant(str(cp))],keywords=[])
   if isinstance(n,ast.Assign)and any(isinstance(x,ast.Name)and x.id=='CONTEXT_SHA'for x in n.targets):n.value=ast.Constant(sha(cp))
 if configure:configure(s,r,argv)
 output_states={q:(q.read_bytes()if q.exists()else None)for q in [r,r.with_suffix('.log'),r.with_name(r.stem+'-source.lean')]}
 ast.fix_missing_locations(t);prior=sys.argv;sys.argv=argv;ok=False;exitcode=None
 try:
  if full:
   def simulate(command,cwd,stdout,stderr):
    assert command==['lake','env','lean',str(s)]and cwd==R/'verification/lean'
    stdout.write(b'SYNTHETIC CONTROLLED SUBPROCESS FIXTURE; NO LEAN COMPILER LAUNCHED.\n')
    return fake(s,r,g)if fake else SimpleNamespace(returncode=0)
   with patch('subprocess.run',simulate):exec(compile(t,str(H),'exec'),g)
  else:exec(compile(t,str(H),'exec'),g);g['guard']()
  ok=True
 except SystemExit as e:exitcode=e.code;ok=e.code==0
 except(AssertionError,ValueError,FileNotFoundError,IsADirectoryError):ok=False
 finally:sys.argv=prior
 assert ok==expect,(label,ok,expect)
 if full:
  d=json.loads(r.read_bytes());assert d['actual_exit_code']==(1 if label=='simulated_lean_failure'else 0)
  assert (d['status']=='passed_actual_tmp_lean_only')==expect
  assert (d['actual_runner_exit_code']==0)==expect
  assert d['canonical_installation_or_aggregate_verification_claimed']is False and d['coverage_complete']is False
  assert d['raw_log_sha256']==sha(r.with_suffix('.log'))
  if label=='simulated_source_drift':assert d['source_unchanged']is False
  if label=='simulated_snapshot_drift':assert d['source_snapshot_sha256']!=d['source_sha256_before']
  if label=='simulated_context_drift':assert d['protection_errors']
 else:
  for q,original in output_states.items():assert (q.read_bytes()if q.exists()else None)==original
 fixtures.append({'fixture':label,'expected_validation_pass':expect,'observed_validation_pass':ok,'synthetic_subprocess_used':full,'actual_lean_compiler_started':False})
case('exact_real_context_prefix')
case('comments_and_strings_masked',source_text='/- outer /- sorry -/ axiom -/\n-- native_decide\nnamespace Prefix\ndef message : String := "unsafe admit sorry"\ntheorem done : True := by trivial\nend Prefix\n')
for token in ['sorry','admit','axiom','unsafe','native_decide','implemented_by','run_elab','ofReduceBool','sorryAx']:
 case('ban_'+token,source_text='namespace Prefix\n'+token+'\nend Prefix\n',expect=False)
case('unclosed_nested_comment',source_text='/- /- sorry -/ ',expect=False)
case('unclosed_string',source_text='def x := "unsafe',expect=False)
case('reject_absolute_context_pin',mutation=lambda c:c['pins_sha256'].update({str(R/'book/coverage/inventory.json'):sha(R/'book/coverage/inventory.json')}),expect=False)
case('reject_traversal_context_pin',mutation=lambda c:c['pins_sha256'].update({'book/../book/coverage/inventory.json':sha(R/'book/coverage/inventory.json')}),expect=False)
case('reject_wrong_owner_hash',mutation=lambda c:c['held_current_source_sha256'].update({'book/coverage/modules.json':'0'*64}),expect=False)
case('reject_wrong_selected_proof_hash',mutation=lambda c:c['held_current_source_sha256'].update({next(iter(proofs)):'0'*64}),expect=False)
case('reject_wrong_current_asset_hash',mutation=lambda c:c['held_current_source_sha256'].update({'SafeLearning/lipsdp.html':'0'*64}),expect=False)
case('reject_wrong_original_audit_hash',mutation=lambda c:c['pins_sha256'].update({c['actual_audit']['file']:'0'*64}),expect=False)
case('reject_wrong_context_status',mutation=lambda c:c.update(status='unverified_context'),expect=False)
case('reject_source_outside_tmp',configure=lambda s,r,a:a.__setitem__(1,str(R/next(iter(proofs)))),expect=False)
case('reject_output_outside_tmp',configure=lambda s,r,a:a.__setitem__(2,str(R/'reports/full-coverage/synthetic-must-not-exist.json')),expect=False)
case('reject_symlink_source',configure=lambda s,r,a:(s.rename(s.with_name('actual.lean')),s.symlink_to(s.with_name('actual.lean'))),expect=False)
case('reject_occupied_record',configure=lambda s,r,a:r.write_text('{}'),expect=False)
# The occupied record fixture is an intentionally created existing file; it remains exactly unchanged.
case('reject_occupied_raw_log',configure=lambda s,r,a:r.with_suffix('.log').write_text('SYNTHETIC OCCUPIED\n'),expect=False)
case('reject_occupied_source_snapshot',configure=lambda s,r,a:r.with_name(r.stem+'-source.lean').write_text('SYNTHETIC OCCUPIED\n'),expect=False)
case('simulated_success',full=True)
case('simulated_lean_failure',full=True,fake=lambda s,r,g:SimpleNamespace(returncode=1),expect=False)
case('simulated_source_drift',full=True,fake=lambda s,r,g:(s.write_text(s.read_text()+'-- synthetic drift\n'),SimpleNamespace(returncode=0))[1],expect=False)
case('simulated_snapshot_drift',full=True,fake=lambda s,r,g:(r.with_name(r.stem+'-source.lean').write_text('-- SYNTHETIC snapshot drift\n'),SimpleNamespace(returncode=0))[1],expect=False)
# Context drift is in a synthetic relocated context only; no production context bytes are changed.
case('simulated_context_drift',full=True,mutation=lambda c:None,fake=lambda s,r,g:(g['CONTEXT'].write_text(g['CONTEXT'].read_text()+'\n'),SimpleNamespace(returncode=0))[1],expect=False)
for n,h in allpins.items():assert sha(R/n)==h,n
assert sha(H)=='f9f9f273bfa7c0f22d78f75fed23d32af794f13d51f329ae06747d3dac691c1a'and sha(C)=='35ac327b8d62c70dd9e0f83236716ee465d9b188cf656c58be97078b3eea5054'
out={'status':'passed_independent_full_current60_owner28_tmp_lean_runner_code_context_and_guard_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(H),'helper_sha256':sha(H),'context':ref(C),'full_actual_code_and_context_read':True,'actual_source_bindings':{'selected_proof_files':1186,'current60_assets':31,'installed_owner28_ledgers':5,'project_pins':6,'provenance_pins':14,'theorems':9896,'fresh_kernel_replay':11,'reused_identical_transitive_dependencies':1175},'working_old_root_aggregate_and_actual_new_frozen28_aggregate_separately_pinned':True,'fixtures':fixtures,'fixture_count':len(fixtures),'simulated_native_records_are_not_genuine_lean_receipts':True,'actual_lean_compiler_started':False,'source_owner_selection_compiler_pub_changed':False,'new_tmp_runner_approved_for_genuine_next_trial':True,'canonical_installation_or_aggregate_verification_claimed':False,'coverage_complete':False}
P=B/'root-current60-owner28-tmp-runner-independent-modules-peer-v1.json';P.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':ref(P),'fixtures':len(fixtures),'actual_lean_compiler_started':False}))
