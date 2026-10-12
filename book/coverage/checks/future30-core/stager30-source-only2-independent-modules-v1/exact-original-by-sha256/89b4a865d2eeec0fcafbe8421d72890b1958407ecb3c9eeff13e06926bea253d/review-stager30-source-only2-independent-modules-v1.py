from pathlib import Path
from datetime import datetime, timezone
import ast,difflib,hashlib,json,subprocess
R=Path('/home/oxrexkevin/SafetyBased');P=R/'reports/book/publication-repo'
O=Path('/tmp/stager30-source-only2-independent-modules-findings-v1.json')
PINS={
 'book/coverage/checks/root_stage_publication30_v2.py':'e991c5ff2376cc155983c85a14a2554c88f9f116ef17ff9455b88e6143d0c234',
 'book/coverage/checks/root_stage_publication30_v1.py':'f6d08fa5d4c114b009ce5bc06444d551522178289867740e93203a32b6e0274c',
 'reports/full-coverage/publication30-browser-document-overlay-v3.json':'f1c2b3892a79ae1e622529399b4be9bcbe0248ae315eb5f55da3f94688b8ae3e',
 'reports/full-coverage/publication30-browser-document-overlay-v2.json':'dd06093d00ee838c079a4c4c48b0c3c1adfa2194087634cc88899cffaeafb82a',
 'reports/full-coverage/publication30-browser-document-overlay-v1.json':'a365e5c91bf1051f3dac357192a4be4cfc7b3313fbd0511adbee76ad1337920d',
 'reports/full-coverage/publication30-prepared-exact-files-v1.json':'165562a84c1a399729c1b8505f8608795df3dd89475eb0c32b81269dfd720d89',
 'reports/full-coverage/checkpoint-30-manifest.json':'74b7eb171018a762341ab671a21d2fd730d171eaa455fa2385b8619a6c9c999a',
 'reports/full-coverage/browser-checkpoint-30-changed-pages-final-v1.json':'ba761ad10ed4fdf24a0247c702d17172b322fda21805ed60646b1cbc34ef432f',
}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(R/n),'bytes':(R/n).stat().st_size}
assert not O.exists() and all(sha(R/n)==h for n,h in PINS.items())
source=(R/'book/coverage/checks/root_stage_publication30_v2.py').read_text();ast.parse(source)
old_source=(R/'book/coverage/checks/root_stage_publication30_v1.py').read_text();ast.parse(old_source)
assert "parser.add_argument('--browser-overlay', required=True)" in source
assert "parser.add_argument('--browser-overlay-sha256', required=True)" in source
assert "assert set(overlay['replacement_root_paths_sha256']) == {'reports/full-coverage/README.md'}" in source
assert "assert n in overlay['replacement_root_paths_sha256']" in source
assert source.count('--literal-pathspecs')==old_source.count('--literal-pathspecs')==2
stream_start='# Read actual staged blob bytes in one process, then SHA256 each exact payload.'
stream_end="assert git(['rev-parse', 'HEAD']).decode().strip() == BASELINE"
def stream(s):return s[s.index(stream_start):s.index(stream_end,s.index(stream_start))]
assert stream(source)==stream(old_source)
o=json.loads((R/'reports/full-coverage/publication30-browser-document-overlay-v3.json').read_bytes())
o2=json.loads((R/'reports/full-coverage/publication30-browser-document-overlay-v2.json').read_bytes())
o1=json.loads((R/'reports/full-coverage/publication30-browser-document-overlay-v1.json').read_bytes())
p=json.loads((R/'reports/full-coverage/publication30-prepared-exact-files-v1.json').read_bytes())
m=json.loads((R/'reports/full-coverage/checkpoint-30-manifest.json').read_bytes())
b=json.loads((R/o['actual_source_exact_changed_pages_report']['file']).read_bytes())
assert o['status']=='actual_source_exact_six_changed_pages_browser_and_corrected_document_overlay_for_staging'
assert o['mathematical_HTML_proofs_assets_or_ledger_bytes_changed'] is False
assert o['original_prepared_publication']['sha256']==PINS['reports/full-coverage/publication30-prepared-exact-files-v1.json']
assert set(o['replacement_root_paths_sha256'])=={'reports/full-coverage/README.md'}
assert p['expected_publication_paths_sha256']['reports/full-coverage/README.md']==o['original_document']['sha256']
assert sha(R/o['preserved_original_document']['file'])==o['original_document']['sha256']
assert not set(o['additional_root_paths_sha256'])&set(p['expected_publication_paths_sha256'])
removed=set(o2['additional_root_paths_sha256'])-set(o['additional_root_paths_sha256'])
assert len(removed)==1 and all(p['expected_publication_paths_sha256'][n]==o2['additional_root_paths_sha256'][n] for n in removed)
for k in ['status','replacement_root_paths_sha256','actual_source_exact_changed_pages_report','mathematical_HTML_proofs_assets_or_ledger_bytes_changed','current_manifest']:
 assert o[k]==o2[k]==o1[k]
for n,h in {**o['replacement_root_paths_sha256'],**o['additional_root_paths_sha256']}.items():
 assert sha(R/n)==h
 assert '.git' not in Path(n).parts and '.lake' not in Path(n).parts and '__pycache__' not in Path(n).parts
 assert '..' not in Path(n).parts and not Path(n).is_absolute()
assert b['status']=='passed_source_exact_all_six_actual_changed_HTML_pages_browser_checks'
assert len(b['actual_changed_HTML_pages'])==len(b['changed_page_checks'])==6
assert b['changed_page_viewport_count']==30
changed=[]
for n,h in m['frozen_inputs_sha256'].items():
 if n.startswith('SafeLearning/') and n.endswith('.html'):
  previous=subprocess.run(['git','--no-optional-locks','show','01b95073d2f78d066ef88c1aa3fd20af1d631e22:'+n],cwd=P,check=True,capture_output=True).stdout
  if hashlib.sha256(previous).hexdigest()!=h:changed.append(n)
assert sorted(changed)==b['actual_changed_HTML_pages']
rootrefs={}
for n,row in b['changed_page_checks'].items():
 q=row['original_row'];assert q['status']=='passed' and q['errors']==[]
 assert q['source_sha256']==m['frozen_inputs_sha256'][n]==sha(R/n)
 assert [v['width'] for v in q['viewports']]==[320,390,768,820,1280]
 assert all(v['documentWidth']<=v['width'] and v['clipped']==[] for v in q['viewports'])
 for r in row['original_report_and_native'].values():
  assert sha(R/r['file'])==r['sha256'];rootrefs[r['file']]=r['sha256']
 nr=row['original_report_and_native']['actual_execution'];nd=json.loads((R/nr['file']).read_bytes())
 assert nd['status']=='passed' and nd['actual_exit_code']==0
 assert sha(R/nd['log'])==nd['log_sha256'];rootrefs[nd['log']]=nd['log_sha256']
 assert nd['helper_sha256_before']==nd['helper_sha256_after']
assert set(b['additional_unchanged_page_checks'])=={'SafeLearning/primer-optimization.html'}
assert b['current_final_css_sha256']==m['frozen_inputs_sha256']['SafeLearning/styles.css']
doc=(R/'reports/full-coverage/README.md').read_text()
assert 'all six actual changed pages at five viewport widths each' in doc
assert 'unchanged optimization primer' in doc and 'separate fresh Primer 0 run' in doc
assert 'does not claim whole-page visual coverage' in doc
assert all(sha(R/n)==h for n,h in PINS.items())
f={'status':'passed_independent_checkpoint30_stager2_full_code_and_actual_source_exact_browser3_document_overlay_review',
 'errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'helper':ref('book/coverage/checks/root_stage_publication30_v2.py'),
 'reviewed_helpers_sha256':{'book/coverage/checks/root_stage_publication30_v2.py':PINS['book/coverage/checks/root_stage_publication30_v2.py']},
 'full_code_read':True,'exact_stager1_to_stager2_delta_read':True,
 'original_unexecuted_stager1_full_mechanical_peer':ref('book/coverage/checks/future30-core/stager30-source-only1-independent-modules-v1/checkpoint30-stager1-full-mechanical-code-review-pending-browser-document-overlay-independent-modules30-closed-peer-v1.json'),
 'actual_browser_document_overlay':ref('reports/full-coverage/publication30-browser-document-overlay-v3.json'),
 'actual_source_exact_changed_pages_report':ref(o['actual_source_exact_changed_pages_report']['file']),
 'actual_changed_HTML_pages_independently_derived_against_Git01b':changed,
 'all30_five_width_changed_page_rows_native0_log_and_source_hashes_checked':True,
 'Optimization_remains_additional_unchanged_QA':True,
 'replacement_scope_only_README_original_target_is_historical_PUB_identity':True,
 'strict_preserved_original_document':ref(o['preserved_original_document']['file']),
 'overlay3_removes_only_already_planned_identical_manual_peer_entry':True,
 'all_additional_paths_disjoint_and_root_physical_hashes_checked':True,
 'literal_NUL_stage_mode_and_streamed_blob_protocol_exactly_preserved':True,
 'bulk_stream_scope_excludes_new_receipt_added_separately':True,
 'current_manifest31_assets1242_proofs_math_and_raw_ledger_bytes_unchanged':True,
 'browser_overlay_native_evidence_refs_checked':rootrefs,
 'code_review_only':True,'stager_producer_or_Git_index_mutation_invoked':False,
 'actual_staging_commit_push_Pages_or_delivery_claimed':False,'coverage_complete':False,
 'scope':'Full stager2 code and actual final overlay3 association review. Prior genuine preparer/6125 initial PUB-byte mechanical review remains exact; final2 validates the original map before the one README replacement and disjoint new QA/native/image paths, then stages only the explicit union. Native report checks derive the six actual changed pages from immutable Git01b and match all current source hashes and thirty passed viewport rows. Historical original_document names the pre-overlay PUB target; its original bytes remain at the explicit strict Root preserved-document alias. No staging/commit/push or full-page image/whole mathematical promotion is inferred.'}
O.write_text(json.dumps(f,indent=2)+'\n')
print(json.dumps({'status':f['status'],'errors':[],'changed_pages':len(changed),'viewport_rows':30,'stager_invoked':False}))
