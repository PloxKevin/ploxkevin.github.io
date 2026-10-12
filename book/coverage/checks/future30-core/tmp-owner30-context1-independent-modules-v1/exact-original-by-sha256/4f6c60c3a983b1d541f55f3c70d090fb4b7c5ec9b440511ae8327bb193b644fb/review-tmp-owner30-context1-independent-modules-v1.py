from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json
R=Path('/home/oxrexkevin/SafetyBased')
H='book/coverage/checks/root_prepare_tmp_owner30_context_v1.py'
T=Path('/tmp/root_tmp_lean_current79_historical_owner29_runner_v1.py')
O=Path('/tmp/tmp-owner30-context1-independent-modules-findings-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(R/n),'bytes':(R/n).stat().st_size}
assert not O.exists()
assert sha(R/H)=='eac90aec1c7c0888f751d04ee7dee64fbf52e9c846a31169d7d945c2c6bb8f65'
assert sha(T)=='15a0e14143ea9338dfa6770840b8bee7a36903889418e785c55b2a2fcdbf2c4e'
s=(R/H).read_text();tree=ast.parse(s)
main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
reference_node=next(n for n in main.body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='references')
references=ast.literal_eval(reference_node.value)
assert len(references)==5
data={n:json.loads((R/n).read_bytes()) for n,h in references.items() if sha(R/n)==h}
assert len(data)==5
selected,manifest,integration,ledger,audit=list(data.values())
assert selected['proof_file_count']==audit['proof_file_count']==len(selected['proof_files'])==1242
assert audit['status']=='passed' and audit['theorem_count']==11080
assert audit['proof_sha256']=={n:r['sha256'] for n,r in selected['proof_files'].items()}
assert len(audit['source_sha256'])==31 and len(audit['checks'])==1245
assert all(c['exit_code']==0 for c in audit['checks'])
assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
assert manifest['source_only_snapshot'] is True and manifest['coverage_complete'] is False
assert integration['applied'] is True and integration['coverage_complete'] is False
owners={r['destination']:r['candidate']['sha256'] for r in integration['exact_replacements']}
assert set(owners)=={'book/coverage/'+n+'.json' for n in ['core','foundations','applied','applied-promotions','modules']}
pins={**references,**audit['proof_sha256'],H:sha(R/H)}
for n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/lean_names.py','verification/lean/verify.py','verification/lean/lean-toolchain','verification/lean/lakefile.toml','verification/lean/lake-manifest.json']:
 pins[n]=sha(R/n)
assert pins['book/coverage/inventory.json']=='9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de'
for n in audit['project_sha256']:
 if n!='verification/lean/SafeLearning.lean':assert pins[n]==audit['project_sha256'][n]
for n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/lean_names.py']:
 assert pins[n]==manifest['frozen_inputs_sha256'][n]
fragments={}
for n,h in owners.items():
 assert sha(R/n)==h==manifest['working_inputs_sha256'][n]
 for f,hf in json.loads((R/n).read_bytes()).get('chapter_fragment_sha256',{}).items():
  assert f.startswith('book/chapters/') and manifest['frozen_inputs_sha256'][f]==hf
  assert f not in fragments or fragments[f]==hf
  fragments[f]=hf
pins.update(fragments)
all_current={**pins,**audit['source_sha256'],**owners}
for n,h in all_current.items():
 p=R/n;assert Path(n).as_posix()==n and not Path(n).is_absolute() and '..' not in Path(n).parts
 assert p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(R)
 assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(R))
 assert sha(p)==h,n
replacement_node=next(n for n in main.body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='replacements')
example_context_sha='0'*64
substitutions=eval(compile(ast.Expression(replacement_node.value),'<exact-code-render-only>','eval'),{'__builtins__':{},'str':str},{'CONTEXT':Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json'),'context_sha':example_context_sha,'STATUS':'actual_source79_final_css_owner30_selected30_audited_TMP_context_only'})
rendered=T.read_text()
assert len(substitutions)==11
for old,new in substitutions.items():assert old in rendered;rendered=rendered.replace(old,new)
ast.parse(rendered)
assert 'historical_source65' not in rendered and 'protected_selected29' not in rendered
assert "command=['lake','env','lean',str(source)]" in rendered
assert "'protected_selected30_proof_sources':1242" in rendered
assert "'actual_installed30_selection':context['selection']" in rendered
assert "'actual_runtime30_final_css_original_audit':context['actual_audit']" in rendered
assert "'installed30_raw_owner_sha256':context['owners_sha256']" in rendered
assert 'ofReduceBool|sorryAx' in rendered and "with snapshot.open('xb')" in rendered
assert "with record.open('x')" in rendered and "with log.open('xb')" in rendered
assert "cwd=ROOT/'verification/lean'" in rendered
assert "canonical_installation_or_aggregate_verification_claimed':False" in rendered
assert all(sha(R/n)==h for n,h in all_current.items())
f={'status':'passed_independent_tmp_actual_source79_finalcss_owner30_context1_full_code_and_rendered_runner_review','errors':[],
 'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'helper':ref(H),'reviewed_helpers_sha256':{H:sha(R/H)},'full_code_read':True,'full_preserved_runner_template_read':True,
 'original_runner_template':{'file':str(T),'sha256':sha(T),'bytes':T.stat().st_size},
 'all_five_exact_actual_context_reference_schemas_checked':{n:ref(n) for n in references},
 'exact_installed_owner30_hashes':owners,'current_selected_source_count':1242,'current_final_css_asset_count':31,
 'current_fragment_count':len(fragments),'all_current_protected_inputs_sha256':all_current,
 'current_project_pins_match_actual_audit_except_distinct_Root_generated_aggregate':True,
 'all_literal_render_substitutions_and_resulting_runner_AST_checked':True,'rendered_runner_executed':False,
 'fresh_TMP_outputs_and_before_after_actual_raw_source_snapshot_logs_preserved':True,
 'forbidden_proof_escape_token_guard_no_named_build_or_cache_output_flag':True,
 'compiler_command_scope':'lake env lean on one absolute TMP source, actual cwd Root verification/lean; no named lake build or -o compiler output',
 'scope':'Full unexecuted context producer and entire previously reviewed runner read. Real installed owner30/current Source79/final-CSS/audit/selection/source-only manifest associations match all1242 selected sources,31 current assets and5 raw owners. Render-only placeholder SHA establishes syntax/protocol without creating a context/runner or executing Lean. Root alone will generate fresh TMP output and publish the actual SHA.',
 'old79_context_or_compiler_invoked':False,'context_producer_invoked':False,'actual_new_context_generated_by_this_reader':False,
 'canonical_owner_source_or_publication_write_invoked':False,'coverage_complete':False}
O.write_text(json.dumps(f,indent=2)+'\n')
print(json.dumps({'status':f['status'],'errors':[],'protected_sources':1242,'assets':31,'owners':5,'fragments':len(fragments),'producer_invoked':False}))
