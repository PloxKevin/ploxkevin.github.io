from pathlib import Path
from datetime import datetime, timezone
import ast,hashlib,json,os,subprocess
R=Path('/home/oxrexkevin/SafetyBased');P=R/'reports/book/publication-repo'
O=Path('/tmp/stager30-source-only1-independent-modules-findings-v2.json')
PIN={
 'book/coverage/checks/root_stage_publication30_v1.py':'f6d08fa5d4c114b009ce5bc06444d551522178289867740e93203a32b6e0274c',
 'reports/full-coverage/publication30-prepared-exact-files-v1.json':'165562a84c1a399729c1b8505f8608795df3dd89475eb0c32b81269dfd720d89',
 'reports/full-coverage/prepare-publication30-source-only-execution-v1.json':'0d97dfe0169a9acc861cdc3a0f6055cac7bb5330cf05310fe767a34ae24bed7f',
 'reports/full-coverage/publication-checks/ledger-checkpoint-30-v1.json':'40d1fde7eabc9857fcda4cd94117ebf8d7ab893380ef86ca8dc17e6946c44408',
 'reports/full-coverage/checkpoint-30-manifest.json':'74b7eb171018a762341ab671a21d2fd730d171eaa455fa2385b8619a6c9c999a',
}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def ref(n):return {'file':n,'sha256':sha(R/n),'bytes':(R/n).stat().st_size}
def git(args):return subprocess.run(['git','--no-optional-locks',*args],cwd=P,check=True,capture_output=True).stdout
assert not O.exists() and all(sha(R/n)==h for n,h in PIN.items())
s=(R/'book/coverage/checks/root_stage_publication30_v1.py').read_text();ast.parse(s)
assert '--literal-pathspecs' in s and '--pathspec-from-file=-' in s and '--pathspec-file-nul' in s
assert "subprocess.Popen(['git', 'cat-file', '--batch']" in s
assert 'tempfile.TemporaryFile()' in s and 'min(1048576, remaining)' in s
assert "assert mode == b'100644'" in s and "assert stage == b'0'" in s
assert 'digest.hexdigest() == expected[n]' in s and "assert process.stdout.read(1) == b'\\n'" in s
prepared=json.loads((R/'reports/full-coverage/publication30-prepared-exact-files-v1.json').read_bytes())
native=json.loads((R/'reports/full-coverage/prepare-publication30-source-only-execution-v1.json').read_bytes())
ledger=json.loads((R/'reports/full-coverage/publication-checks/ledger-checkpoint-30-v1.json').read_bytes())
manifest=json.loads((R/'reports/full-coverage/checkpoint-30-manifest.json').read_bytes())
assert prepared['status']=='exact_checkpoint30_publication_inputs_prepared_awaiting_staging_and_delivery'
expected=prepared['expected_publication_paths_sha256']
assert expected and all(sha(P/n)==h for n,h in expected.items())
assert native['status']=='passed' and native['actual_exit_code']==0
assert native['actual_command'][1]=='book/coverage/prepare_publication30_source_only_v3.py'
assert sha(R/native['log'])==native['log_sha256']
assert native['helper_sha256_before']==native['helper_sha256_after']=={'book/coverage/prepare_publication30_source_only_v3.py':'f1b8f6ab8c8cceaa0323de4097c2292ce78b1eecfa3ce0297f5cae4f8237e3bb'}
assert ledger['integrity_status']=='passed' and ledger['errors']==[] and ledger['mathematical_coverage_complete'] is False
assert ledger['counts']['material_review_statuses']=={'reviewed':4770,'pending':8004}
for d in ledger['domains']:assert d['ledger_sha256']==expected['book/coverage/'+d['domain']+'.json']
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31 and all(expected[n]==h for n,h in assets.items())
proofs={p.relative_to(P).as_posix():sha(p) for p in (P/'verification/lean/SafeLearning').glob('*.lean') if p.name!='Smoke.lean'}
assert proofs=={n:r['sha256'] for n,r in manifest['proof_files'].items()} and len(proofs)==1242
assert git(['rev-parse','HEAD']).decode().strip()=='01b95073d2f78d066ef88c1aa3fd20af1d631e22'
assert git(['diff','--cached','--name-only','-z'])==b''
rows=[r for r in git(['status','--porcelain','-z','--untracked-files=all']).decode().split('\0') if r]
assert all(r[:2] in {' M','??'} and r[3:] in expected for r in rows)
exclusions=[l[4:] for l in (P/'_config.yml').read_text().splitlines() if l.startswith('  - ')]
assert exclusions==sorted(set(exclusions))
website=0
for directory,subdirs,files in os.walk(P):
 rel=Path(directory).relative_to(P).as_posix()
 subdirs[:]=[n for n in subdirs if n!='.git' and (rel+'/'+n if rel!='.' else n) not in exclusions]
 for n in files:
  p=Path(directory)/n;name=p.relative_to(P).as_posix()
  if any(name==e or name.startswith(e+'/') for e in exclusions):continue
  assert not p.is_symlink();website+=p.stat().st_size
assert website<850000000
assert all(sha(R/n)==h for n,h in PIN.items())
f={'status':'passed_independent_checkpoint30_stager1_full_mechanical_code_review_pending_corrected_browser_docs_overlay',
 'errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'helper':ref('book/coverage/checks/root_stage_publication30_v1.py'),
 'reviewed_helpers_sha256':{'book/coverage/checks/root_stage_publication30_v1.py':PIN['book/coverage/checks/root_stage_publication30_v1.py']},
 'full_code_read':True,'exact_prepared_copy_native_and_partial_publication_ledger_schemas_checked':True,
 'all_prepared_publication_sha256_bytes_checked':True,'actual_prepared_path_count':len(expected),'exact_publication_1242_proofs_and31_assets_checked':True,
 'actual_prepared_whitelist':ref('reports/full-coverage/publication30-prepared-exact-files-v1.json'),
 'actual_preparer_native':ref('reports/full-coverage/prepare-publication30-source-only-execution-v1.json'),
 'actual_publication_ledger':ref('reports/full-coverage/publication-checks/ledger-checkpoint-30-v1.json'),
 'literal_NUL_pathspec_and_100644_stage0_scope_read':True,
 'streamed_cat_file_exact_OID_kind_size_payload_SHA_and_separator_protocol_read':True,
 'streamed_input_query_file_avoids_full_archive_capture':True,
 'physical_path_and_git_cache_snapshot_boundaries_read':True,
 'before_stage_all_dirty_rows_must_be_explicit_and_cached_index_empty':True,
 'current_publication_baseline_head':'01b95073d2f78d066ef88c1aa3fd20af1d631e22',
 'observed_pre_staging_website_bytes':website,'observed_exclusions_count':len(exclusions),
 'website_byte_limit':850000000,'code_review_only':True,'stager_invoked':False,
 'Git_index_stage_commit_push_or_publication_write_invoked':False,
 'actual_docs1_browser_claim_or_full_delivery_approved':False,
 'Root_source_exact_changed_page_browser_QA_and_docs_overlay_pending':True,
 'scope':'Full unexecuted stager1 mechanical code review and genuine initial prepared-file/ledger/native/publication byte association only. Parent has identified that docs1 browser composition omitted changed Primer0 and included unchanged Optimization. This peer does not approve that document assertion or invoke staging; new docs/delivery overlay and final stager2 must be independently bound before Root stages. Original stager1 remains unexecuted historical.',
 'coverage_complete':False}
O.write_text(json.dumps(f,indent=2)+'\n')
print(json.dumps({'status':f['status'],'errors':[],'prepared_paths':len(expected),'website_bytes':website,'stager_invoked':False}))
