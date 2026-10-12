from pathlib import Path
import ast,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased'); H=R/'book/coverage/checks/root_prepare_source81_owner30_tmp_context_v1.py'
O=Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json'); T=Path('/tmp/root_tmp_lean_current79_owner30_finalcss_runner_v1.py')
A=R/'reports/full-coverage/source80-81-corrections-application-v3.json'; N=R/'reports/full-coverage/source80-81-actual-application-execution-v1.json'
OUT=Path('/tmp/source81-owner30-context-independent-modules31-findings-v2.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def path(r):
 p=Path(r['file']);return p if p.is_absolute()else R/p
assert sha(H)=='f66367bdc17a2a7c6169dde0ca950138086e3dea8dbabeb56e8c3529712d180e'
assert sha(O)=='73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
assert sha(T)=='82861b9eb3cbd7bccbb6bc7662de6972bc67cfc0548807a6f2983402b0ded281'
assert sha(A)=='1bffcd1551d55ec24980a37915de9965b3852f25ac3ca554d3350fee435ba9d1'
code=H.read_text(); tree=ast.parse(code);old=json.loads(O.read_bytes());app=json.loads(A.read_bytes());native=json.loads(N.read_bytes())
assert native['actual_exit_code']==0 and native['status']=='passed'
for p,h in native['helper_sha256_before'].items():assert sha(R/p)==h==native['helper_sha256_after'][p]
assert sha(R/native['log'])==native['log_sha256']
assert app['status']=='passed_actual_reviewed_source80_81_two_corrections_owner_rebase_pending'and app['coverage_complete']is False
assert app['1242_selected_proofs_and_five_raw_owner30_files_unchanged']is True
assert [x['correction_id']for x in app['applications']]==[80,81]
assert [x['source']for x in app['applications']]==['SafeLearning/primer-linalg.html','SafeLearning/nn-in-the-loop.html']
refs=[ref(H),ref(O),ref(T),ref(A),ref(N),ref(R/native['log'])]
changed={'SafeLearning/primer-linalg.html','SafeLearning/nn-in-the-loop.html','book/coverage/inventory.json','book/coverage/material-corrections.json'}
guards={**old['pins_sha256'],**old['held_current_source_sha256'],**old['owners_sha256']}
observed_changes={n for n,h in guards.items()if sha(R/n)!=h};assert observed_changes==changed
new_guards={n:sha(R/n)if n in changed else h for n,h in guards.items()}
def guard():
 assert sha(H)==refs[0]['sha256']and sha(O)==refs[1]['sha256']and sha(T)==refs[2]['sha256']and sha(A)==refs[3]['sha256']
 for n,h in new_guards.items():
  p=R/n;assert not Path(n).is_absolute()and'..'not in Path(n).parts and p.resolve().is_relative_to(R)and p.is_file()and not p.is_symlink()and sha(p)==h,n
 for x in refs:assert sha(path(x))==x['sha256']
guard()
for row in app['applications']:
 assert sha(R/row['source'])==row['after_sha256']
 for key in ['inventory_before','inventory_after','source_proposal','independent_semantic_review','actual_fresh_parser','historical_source']:
  x=row[key];assert sha(path(x))==x['sha256'];refs.append(x)
 oldbytes=path(row['historical_source']).read_bytes();current=(R/row['source']).read_bytes();s=oldbytes.decode()
 for rep in row['replacements']:assert s.count(rep['before'])==1;s=s.replace(rep['before'],rep['after'],1)
 assert s.encode()==current
 pn=json.loads(path(row['actual_fresh_parser']).read_bytes());assert pn['actual_exit_code']==0 and pn['both_parser_ROOT_and_OUT_strictly_TMP']is True
 assert sha(path(pn['log']))==pn['log']['sha256'];refs.append(pn['log'])
assert sha(R/'book/coverage/inventory.json')=='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
assert sha(R/'book/coverage/inventory.json')==app['applications'][-1]['inventory_after']['sha256']
assert len(json.loads((R/'book/coverage/material-corrections.json').read_bytes())['corrections'])==81
assert len(old['held_current_source_sha256'])==31 and len(old['owners_sha256'])==5
selected=json.loads((R/'reports/full-coverage/checkpoint-30-selection.json').read_bytes())
assert len(selected['proof_files'])==1242
for n,row in selected['proof_files'].items():
 assert new_guards[n]==row['sha256']
outputs=[Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json'),Path('/tmp/root_tmp_lean_current81_historical_owner30_runner_v1.py'),R/'reports/full-coverage/source81-owner30-tmp-context-preparation-v1.json']
for p in outputs:
 assert not p.exists()and not p.is_symlink()
 assert all(not a.is_symlink()for a in p.parents)
 # Exclusive outputs are fixed names, not supplied paths; actual parents are physically safe.
 assert p.parent.resolve()==p.parent
imports={x.name for node in ast.walk(tree)if isinstance(node,ast.Import)for x in node.names}
assert imports=={'hashlib','json'}and not any(isinstance(x,ast.ImportFrom)and x.module in ['subprocess','importlib']for x in ast.walk(tree))
assert "with p.open('xb')"in code and 'compile(rendered, str(RUNNER)'in code
replacements=[(str(O),str(outputs[0])),(refs[1]['sha256'],'0'*64),
('actual_source79_final_css_owner30_selected30_audited_TMP_context_only','actual_source81_with_unchanged_raw_source79_owner30_for_tmp_trials_only'),
('actual_source79_final_css_owner30_context','actual_source81_historical_source79_owner30_context'),
('unchanged_current79_final_css_book_assets','unchanged_current81_final_css_book_assets'),
('Run a genuine TMP Lean trial under the actual Source79 final CSS and raw owner30 context.','Run a genuine TMP Lean trial under actual Source81 and unchanged raw Source79 owner30.')]
s=T.read_text()
for before,after in replacements:assert s.count(before)==1;s=s.replace(before,after,1)
compile(s,'<independent-static-source81-render-check>','exec');ast.parse(s)
assert s.count("command=['lake','env','lean',str(source)]")==1
assert 'protected_selected30_proof_sources\':1242'in s and 'unchanged_current_source79_raw_owner30_files\':5'in s
for clause in ["'owner_identity_rebase_pending': True","'aggregate_source81_verification_claimed': False","'coverage_complete': False"]:assert clause in code
assert code.count('write_new(')==4
# Full source and all functions were read by the reviewer; this is actual static/input verification, not producer execution.
guard()
findings={'status':'passed_independent_source81_historical_owner30_tmp_context_full_code_actual_input_review','errors':[], 'helper':ref(H),'full_code_read':True,'reviewed_helpers_sha256':{ref(H)['file']:sha(H)},'actual_application':ref(A),'actual_application_native':ref(N),'old_context':ref(O),'old_runner':ref(T),'source81_inventory_sha256':sha(R/'book/coverage/inventory.json'),'exact_changed_current_identity_keys':sorted(changed),'all_protected_current_sha256':new_guards,'actual_input_refs':refs,'protected_selected30_proof_sources':1242,'current_source81_final_css_assets':31,'unchanged_historical_source79_raw_owner30_files':5,'six_literal_template_replacements_verified':True,'rendered_runner_Python_compile_without_execution_passed':True,'exclusive_fixed_outputs_and_actual_nonsymlink_parents_verified':True,'literal_kernel_invocation_and_standard_oracle_scan_unchanged':True,'actual_old_context_and_runner_bytes_unchanged':True,'source81_owner_rebase_claimed':False,'source81_aggregate_verification_claimed':False,'producer_or_Lean_or_dependency_mutation':False,'protection_errors':[],'scope':'Full static helper/old-runner read plus genuine actual Source81 current-identity checks. Producer remains unexecuted; rendered runner was compiled only as Python syntax, never imported or run. Historical auditedSource79 owner30 and selected30 proof provenance remains explicit.'}
with OUT.open('x')as f:json.dump(findings,f,indent=2);f.write('\n')
print(json.dumps({'status':findings['status'],'findings':ref(OUT),'guards':len(new_guards),'errors':[]}))
