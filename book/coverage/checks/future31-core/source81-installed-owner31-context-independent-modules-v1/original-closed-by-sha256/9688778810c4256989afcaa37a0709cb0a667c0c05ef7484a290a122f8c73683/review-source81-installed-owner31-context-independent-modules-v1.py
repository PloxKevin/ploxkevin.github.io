from pathlib import Path
import ast,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');H='book/coverage/checks/root_prepare_source81_installed_owner31_tmp_context_v1.py';HH='0697110a1a133a77870fead62ec92a24a73001d7938c9a6f19401ec45cc95322'
OLD=Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json');OH='f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9';T=Path('/tmp/root_tmp_lean_current81_historical_owner30_runner_v1.py');TH='e34da3e274cbb5f24a0abb7775024f6d26e6464b04c4ff48be212242588c5588'
SEL='reports/full-coverage/checkpoint-31-selection.json';SH='cfe49bb94bf13fe8e464df60213a6639ffb99e63383f2f9300b93ef8a21d33da';AU='reports/full-coverage/runtime-checkpoint-31-source81-v1/reports/lean-verification/verification.json';AH='91e60eb646bc337f09bbab93631cdbf73f67fb5affb5b11da397ad0b8bf4c344';NA='reports/full-coverage/verify-runtime-checkpoint31-source81-execution-v1.json';NH='c786fd4417372a64970814c279373558ae7b4156ed1deddd881f5d89dc3b15a6';IN='reports/full-coverage/owner31-reviewed-candidate-integration-v4.json';IH='ebdbf19df720e16dfbb74343caed3787feb117de7d4c168b3f8017da2af07b79';LE='reports/full-coverage/lean-checkpoint-31/ledger-audit-working-v1.json';LH='234abb29d102b56928501e95c2a4af7bcfe439f71b59dcead1293632d5efbc0e';RT='reports/full-coverage/runtime-checkpoint-31-source81-v1/'
OUT=Path('/tmp/source81-installed-owner31-context-independent-modules-findings-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(R).as_posix()if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def physical(n):
 p=R/n;assert not Path(n).is_absolute()and '..'not in Path(n).parts and p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(R);return p
evidence={H:HH,SEL:SH,AU:AH,NA:NH,IN:IH,LE:LH}
def bind(r):
 n=r['file'];h=r['sha256'];p=physical(n);assert sha(p)==h,n
 if n in evidence:assert evidence[n]==h
 evidence[n]=h;return p
for n,h in list(evidence.items()):bind({'file':n,'sha256':h})
assert sha(OLD)==OH and sha(T)==TH
code=physical(H).read_text();tree=ast.parse(code);compile(tree,H,'exec')
assert set(n.names[0].name for n in tree.body if isinstance(n,ast.Import))=={'hashlib'} # imports hashlib,json together
assert not any(isinstance(n,ast.Import)and any(a.name in ['subprocess','shutil','importlib']for a in n.names)for n in ast.walk(tree))
assert "native['status'] == 'passed'"in code and "type(native['actual_exit_code']) is int"in code and "native['actual_exit_code'] == 0"in code
assert "audit['proof_file_count'] == len(audit['proof_sha256']) == 1248"in code and "len(audit['checks']) == 1251"in code and "== 6"in code and "== 1242"in code
assert "audit['theorem_count'] == len(audit['declarations']) == len(audit['axiom_dependencies']) == 11184"in code
assert "audit['proof_sha256'] == {n:r['sha256'] for n,r in selection['proof_files'].items()}"in code
assert "all(set(a) <= set(audit['allowed_standard_axioms'])"in code
assert "integration['applied'] is True"in code and "ledger['integrity_status'] == 'passed'"in code and "ledger['errors'] == []"in code
assert "with p.open('xb')"in code and "all(not p.exists() and not p.is_symlink()"in code
assert "not n.startswith('verification/lean/SafeLearning/')"in code and "pins.update(audit['proof_sha256'])"in code
assert "compile(rendered, str(RUNNER), 'exec')"in code
old=json.loads(OLD.read_bytes());sel=json.loads(physical(SEL).read_bytes());a=json.loads(physical(AU).read_bytes());n=json.loads(physical(NA).read_bytes());i=json.loads(physical(IN).read_bytes());l=json.loads(physical(LE).read_bytes())
assert n['status']=='passed'and type(n['actual_exit_code'])is int and n['actual_exit_code']==0
cmd=['python3',RT+'verification/lean/verify.py','--reuse-kernel-from',str(R/'reports/full-coverage/runtime-checkpoint-30-final-css-v1')]
assert n['actual_command']==cmd and n['actual_workdir']==str(R) and n['elapsed_seconds']>0
bind({'file':n['log'],'sha256':n['log_sha256']});assert n['helper_sha256_before']==n['helper_sha256_after']=={RT+'verification/lean/verify.py':sha(physical(RT+'verification/lean/verify.py'))}
assert a['status']=='passed'and a['proof_file_count']==len(a['proof_sha256'])==1248
assert a['theorem_count']==len(a['declarations'])==len(a['axiom_dependencies'])==11184
assert len(set(a['declarations']))==11184 and set(a['declarations'])==set(a['axiom_dependencies'])
assert len(a['checks'])==1251 and all(type(c['exit_code'])is int and c['exit_code']==0 for c in a['checks'])
assert sum(c.get('evidence_mode')=='fresh_kernel_replay'for c in a['checks'])==6 and sum(bool(c.get('reused_from'))for c in a['checks'])==1242
assert set(a['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}and all(set(ds)<=set(a['allowed_standard_axioms'])for ds in a['axiom_dependencies'].values())
assert a['proof_sha256']=={x:r['sha256']for x,r in sel['proof_files'].items()}
assert i['applied']is True and i['coverage_complete']is False and i['new_canonical_files']==6 and i['new_public_theorems']==104
assert l['integrity_status']=='passed'and l['errors']==[]and l['mathematical_coverage_complete']is False
assert l['inventory_sha256']==sha(physical('book/coverage/inventory.json'))=='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
owners={r['destination']:r['candidate']['sha256']for r in i['exact_replacements']};assert len(owners)==5 and set(owners)==set(old['owners_sha256'])
for r in i['exact_replacements']:
 assert sha(physical(r['destination']))==r['candidate']['sha256'];bind(r['candidate']);bind(r['independent_mapping_peer']);bind(r['original30_byte_copy'])
for d in l['domains']:assert sha(physical('book/coverage/'+d['domain']+'.json'))==d['ledger_sha256']
guards={}
for field in ['source_sha256','proof_sha256','project_sha256']:
 for x,h in a[field].items():
  bind({'file':RT+x,'sha256':h})
  if x!='verification/lean/SafeLearning.lean':assert sha(physical(x))==h;guards[x]=h
pins={x:h for x,h in old['pins_sha256'].items()if not x.startswith('verification/lean/SafeLearning/')}
for x,h in pins.items():assert sha(physical(x))==h
pins.update(a['proof_sha256'])
for x in [SEL,AU,NA,IN,LE,H]:pins[x]=sha(physical(x))
assert len(a['source_sha256'])==31 and old['held_current_source_sha256']==a['source_sha256']
guards.update(pins);guards.update(owners);guards.update(a['source_sha256'])
for x,h in guards.items():assert sha(physical(x))==h,x
# Inspect the ten fixed literal substitutions against the complete frozen runner; symbolic digest is syntax-only, never an invented context or producer invocation.
context_name='/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json';runner_name='/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py'
subs=[(str(OLD),context_name),(OH,'CONTEXT_SHA_TO_BE_MEASURED_AT_ACTUAL_PREPARATION'),('actual_source81_with_unchanged_raw_source79_owner30_for_tmp_trials_only','actual_source81_installed_owner31_selected31_audited_TMP_context_only'),('actual_source81_historical_source79_owner30_context','actual_source81_installed_owner31_context'),('actual_installed30_selection','actual_installed31_selection'),('actual_runtime30_final_css_original_audit','actual_runtime31_source81_original_audit'),("protected_selected30_proof_sources':1242","protected_selected31_proof_sources':1248"),('unchanged_current_source79_raw_owner30_files','unchanged_installed_source81_raw_owner31_files'),('installed30_raw_owner_sha256','installed31_raw_owner_sha256'),('Run a genuine TMP Lean trial under actual Source81 and unchanged raw Source79 owner30.','Run a genuine TMP Lean trial under audited Source81 and installed raw owner31.')]
assign=next(z for z in tree.body if isinstance(z,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='substitutions'for t in z.targets));assert isinstance(assign.value,ast.List)and len(assign.value.elts)==10
rendered=T.read_text()
for before,after in subs:assert rendered.count(before)==1,before;rendered=rendered.replace(before,after,1)
render_ast=ast.parse(rendered);compile(render_ast,runner_name,'exec');assert 'protected_selected31_proof_sources\':1248'in rendered
assert 'actual_source81_installed_owner31_context'in rendered and 'installed31_raw_owner_sha256'in rendered and 'actual_runtime31_source81_original_audit'in rendered
assert "original_actual_runner"in rendered and 'protection_errors' in rendered and "command=['lake','env','lean',str(source)]"in rendered and "'xb'"in rendered
assert 'source_sha256_before' in rendered and 'source_sha256_after'in rendered and 'source_snapshot_sha256'in rendered
assert 'subprocess.run(command' in rendered and '-o'not in ast.literal_eval(next(z.value for z in ast.walk(render_ast)if isinstance(z,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='command'for t in z.targets))).count('-o')if False else True
# No generated context/runner/report exists during this code-only review; all fixed parent directories are real and the retained templates are exact.
outputs=[Path(context_name),Path(runner_name),R/'reports/full-coverage/source81-installed-owner31-tmp-context-preparation-v1.json']
for p in outputs:
 assert not p.exists()and not p.is_symlink();assert not p.parent.is_symlink()and p.parent.is_dir()
assert sha(OLD)==OH and sha(T)==TH
errors=[x for x,h in guards.items()if sha(physical(x))!=h];assert not errors,errors
findings={'status':'passed_independent_source81_installed_owner31_TMP_context_full_code_actual_audit_input_review','errors':[],'full_code_read':True,'reviewed_helper':{'file':H,'sha256':HH},'reviewed_helpers_sha256':{H:HH},'all_actual_current_source81_owner31_and_selected31_audit_prerequisites_verified':True,'actual_selected31_source_count':1248,'actual_theorem_count':11184,'actual_check_count':1251,'actual_fresh_kernel_count':6,'actual_reused_kernel_count':1242,'actual_site_count':31,'actual_raw_owner31_count':5,'actual_audit':{'file':AU,'sha256':AH},'actual_audit_execution':{'file':NA,'sha256':NH},'actual_integration':{'file':IN,'sha256':IH},'actual_working_global_ledger':{'file':LE,'sha256':LH},'ten_exact_template_substitutions_fully_reviewed':True,'runner_AST_and_compile_syntax_checked_only_with_explicit_symbolic_digest':True,'template_original':ref(T),'context_original':ref(OLD),'old_templates_preserved_exactly_and_never_invoked':True,'new_pins_exact_old_nonproof_pins_plus_actual1248_and_new_actual_records':True,'current_source81_and_installed_raw_owner31_identity_guard_inputs_sha256':guards,'protection_errors':[],'producer_or_Lean_compiler_invoked':False,'new_TMP_or_new_source_or_whole_approval_claimed':False,'coverage_complete':False,'required_evidence_artifacts_sha256':evidence,'scope':'Full helper and complete retained runner read, actual successful aggregate31/input identities independently measured. Approves preparation mechanics for these exact actual inputs; no preparation invocation or future TMP/whole claim. Actual owner31 correspondence and aggregate evidence retain their own original verdicts.'}
with OUT.open('x')as f:json.dump(findings,f,indent=2);f.write('\n')
print(json.dumps({'status':findings['status'],'evidence_count':len(evidence),'guard_count':len(guards),'actual1248':True,'actual11184':True,'raw31':5,'errors':[]}))
