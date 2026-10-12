from pathlib import Path
import ast, hashlib, importlib.util, json, subprocess
R = Path('/home/oxrexkevin/SafetyBased')
B = R/'book/coverage/checks/future29-core/pages29-config2-independent-modules-v1'
H = R/'book/coverage/checks/root_prepare_pages29_config_v2.py'
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p): return {'file':p.relative_to(R).as_posix(),'sha256':digest(p)}
assert digest(H) == 'b4ccaeca493d0cfd80ed5c8ae5f32ecb8015250e1175e9631afb2312b3ff5ea1'
ast.parse(H.read_text())
spec=importlib.util.spec_from_file_location('independent_pages29_config2_no_main',H)
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
P=R/'reports/book/publication-repo'
original=(P/'_config.yml').read_bytes()
assert hashlib.sha256(original).hexdigest()==m.BEFORE=='dd0800b1b4364dfae50b78ab504e6f669c9784847d041c84289e2474dabf189b'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==m.HEAD
old={s[4:] for s in original.decode().splitlines() if s.startswith('  - ')}
assert len(old)==177 and original.decode()==m.HEADER+''.join('  - '+n+'\n' for n in sorted(old))
legacy=R/m.LEGACY156
assert digest(legacy)==m.LEGACY156_SHA=='1f8ac723695777fc029ec267efab2141978b11f3c8b0604aebcfb9d9d953e7bd'
old156={s[4:] for s in legacy.read_text().splitlines() if s.startswith('  - ')}
assert len(old156)==156 and old156<=old
assert m.ADDITIONS=={'reports/full-coverage/publication-prepared-29-files.json'}
assert m.REMOVALS=={'book/coverage/checks/future29-foundations'}
new=(old-m.REMOVALS)|m.ADDITIONS
assert len(new)==177 and old156<=new and 'book/coverage/checks' in new
assert not m.kept('book/coverage/checks/future29-foundations/anything.json',new)
assert not m.kept('reports/full-coverage/publication-prepared-29-files.json',new)
for n in new: m.safe(P,n)
for n in [m.REPORT,m.BACKUP]: assert not (R/n).exists() and not (P/n).exists()
manifest=json.loads((R/'reports/full-coverage/checkpoint-29-manifest.json').read_bytes())
selection=json.loads((R/'reports/full-coverage/checkpoint-29-selection.json').read_bytes())
audit=json.loads((R/'reports/full-coverage/lean-checkpoint-29/verification-original.json').read_bytes())
assert manifest['status']=='formal_verification_passed_partial_coverage' and audit['status']=='passed'
assert manifest['selection_sha256']==digest(R/'reports/full-coverage/checkpoint-29-selection.json')
assert manifest['proof_files']==selection['proof_files']
assert len(selection['proof_files'])==audit['proof_file_count']==1197
assert audit['theorem_count']==len(audit['declarations'])==len(audit['axiom_dependencies'])==10114
assert len(audit['checks'])==1200 and all(type(x['exit_code']) is int and x['exit_code']==0 for x in audit['checks'])
assert sum(x.get('evidence_mode')=='fresh_kernel_replay' for x in audit['checks'])==11
assert sum(x.get('evidence_mode')=='reused_identical_module_and_transitive_local_imports' for x in audit['checks'])==1186
assert set(audit['allowed_standard_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert all(set(v)<=set(audit['allowed_standard_axioms']) for v in audit['axiom_dependencies'].values())
assert manifest['successful_verification']['report_sha256']==digest(R/'reports/full-coverage/lean-checkpoint-29/verification-original.json')
assert audit['proof_sha256']=={n:v['sha256'] for n,v in selection['proof_files'].items()}
for n,v in selection['proof_files'].items(): assert digest(R/n)==digest(P/n)==v['sha256']
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31
for n,h in assets.items(): assert m.kept(n,new) and digest(R/n)==digest(P/n)==h
browser=json.loads((R/'reports/full-coverage/browser-checkpoint-29.json').read_bytes())
assert browser['source_sha256']==assets
assert (browser['page_count'],browser['verified_viewport_count'],browser['fresh_verified_viewport_count'],browser['retained_verified_viewport_count'])==(29,145,20,125)
ledger=json.loads((P/'reports/full-coverage/lean-checkpoint-29/ledger-audit.json').read_bytes())
assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
assert ledger['counts']['material_review_statuses']=={'reviewed':4663,'pending':8111}
assert ledger['inventory_sha256']=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
registry=R/'reports/full-coverage/publication-prepared-29-files.json'; assert registry.is_file()
B.mkdir(parents=True,exist_ok=True)
archive=B/'actual-previous177-config-dd0800-original.yml'
assert not archive.exists()
with archive.open('xb') as f: f.write(original)
assert digest(archive)==m.BEFORE
peer={'status':'passed_independent_pages29_archival_configuration2_full_code_review','errors':[],
 'helper':ref(H),'helper_sha256':digest(H),'actual_old_config':ref(archive),
 'actual_old_config_original_live_path_historical_metadata':'reports/book/publication-repo/_config.yml',
 'reviewed_configuration_delta':{'old_count':177,'new_count':177,'retained_original156':156,'removed_redundant_child':sorted(m.REMOVALS),'added_generated_registry':sorted(m.ADDITIONS),'removed_child_still_excluded_by_parent':'book/coverage/checks'},
 'direct_full_source_review':True,'code_review_findings':[
 'Literal command-free read confirms unchanged audit, selected-source, browser, ledger and 850MB gates; only exact177-to177 exclusion swap and versioned backup/report fields differ.',
 'All original156 exclusions remain; parent book/coverage/checks still excludes the removed redundant child. Generated registry remains exact in Git and is excluded only from the website.',
 'Prospective size calculation accounts for changed config plus exact backup and report fixed point. Actual budget readiness and apply must be executed by Root; this reviewer did not invoke main or a producer.',
 'Exclusive Root and PUB backup/report creation precedes the only PUB config write; source/owner/canonical files are read-only. Actual delivery remains pending.'],
 'actual_audit':ref(R/'reports/full-coverage/lean-checkpoint-29/verification-original.json'),
 'exact_generated_registry_in_git':ref(registry),
 'legacy156':ref(legacy),
 'original_full_pages29_v1_peer':ref(R/'book/coverage/checks/future29-core/pages29-config-independent-modules-v1/pages29-config-full-independent-modules29-closed-peer-v2.json'),
 'original_pages29_v1_byte_alias_interface':ref(R/'book/coverage/checks/future29-core/pages29-config-independent-modules-v1/old-config-byte-alias-interface-v3/pages29-config-full-independent-modules29-byte-alias-closed-interface-v3.json'),
 'future_actual_preparation_and_delivery_approved':False,'coverage_complete':False,
 'supplementary_after_frozen29_manifest':True}
out=Path('/tmp/pages29-config2-independent-modules-peer-v1.json')
assert not out.exists(); out.write_text(json.dumps(peer,indent=2)+'\n')
print(json.dumps({'status':peer['status'],'errors':[],'actual_old_config':peer['actual_old_config'],'helper_sha256':digest(H)}))
