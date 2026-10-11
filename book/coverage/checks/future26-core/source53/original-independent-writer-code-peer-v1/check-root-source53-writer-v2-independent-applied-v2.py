from pathlib import Path
from datetime import datetime, timezone
import ast, contextlib, hashlib, importlib.util, io, json, sys, tempfile
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
ref=lambda p:{'file':str(p),'sha256':H(p)}
helper=ROOT/'book/coverage/checks/root_apply_source53_v2.py'
old_helper=ROOT/'book/coverage/checks/root_apply_source53_v1.py'
assert H(helper)=='20d5933637d720bdd263838f2af361425d4aa730e6ad33d721e61f5c625d481e'
assert H(old_helper)=='e642b92c44bf0c3e073feed395726b9ebd95202cf2297d654ecc47817d12c76e'
oldline="    assert [row['correction_id'] for row in corrections['corrections']] == list(range(1, 53))\n"
newlines="    assert sha(corrections_path) == 'c107b4732f6b5244ac3620f721e1ade9e00691f0b6f126180a06afa1ac82b355'\n    assert all('correction_id' not in row for row in corrections['corrections'][:9])\n    assert [row['correction_id'] for row in corrections['corrections'][9:]] == list(range(10, 53))\n"
assert helper.read_text().count(newlines)==old_helper.read_text().count(oldline)==1
assert helper.read_text().replace(newlines,oldline,1)==old_helper.read_text()
tree=ast.parse(helper.read_text());compile(helper.read_text(),str(helper),'exec')
main=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='main')
mutable=[]
for node in ast.walk(main):
 if isinstance(node,ast.Call)and isinstance(node.func,ast.Attribute)and node.func.attr in['write_text','write_bytes']:
  target=ast.unparse(node.func.value)
  if isinstance(node.func.value,ast.Name):mutable.append((target,node.func.attr))
  else:assert target.startswith("isolated / 'SafeLearning'") and node.func.attr=='write_text'
assert sorted(mutable)==[('corrections_path','write_bytes'),('inventory_path','write_bytes'),('source','write_text')]
text=helper.read_text()
assert text.index('# All guards and the independent full parser have passed before first write.')<text.index('    copies = {}')<text.index('    source.write_text(new_text)')
assert "assert type(actual['actual_exit_code']) is int and actual['actual_exit_code'] == 0" in text
assert "'checkpoint25_pushed_actual_pages_build_and_all31_live_hashes_verified_coverage_remains_partial'" in text
assert "assert row['http_status'] == 200 and row['matches'] is True" in text
assert "'publication25-content-push-execution-v1'" in text and "'publication25-delivery-metadata-push-execution-v1'" in text
proposal_path=Path('/tmp/foundations-hertneck-and-scenario-source53-qualification-proposal26-v1.json')
peer_path=Path('/tmp/hertneck-scenario-source53-independent-applied-semantic-and-full-parser-review26-v1.json')
assert H(proposal_path)=='9b3018d98c731db5f708f588aa69cfc8d1da1bd51d88375055a6c584d37d3323'
assert H(peer_path)=='349044d041663e5aaf6f59307297b4f01406d01c3a578d8544f2955f3c20a40e'
proposal,peer=read(proposal_path),read(peer_path)
assert peer['proposal_approved']is True and peer['errors']==[]
assert peer['entire_original_proposal_body_and_preparation_time']==proposal
assert peer['proposal']==ref(proposal_path)
assert len(proposal['replacements'])==len(peer['replacement_decisions'])==4
assert all(r['approved']is True and r['missing_clauses']==[]for r in peer['replacement_decisions'])
corrections_path=ROOT/'book/coverage/material-corrections.json';corrections=read(corrections_path)
assert H(corrections_path)=='c107b4732f6b5244ac3620f721e1ade9e00691f0b6f126180a06afa1ac82b355'
assert len(corrections['corrections'])==52
assert all('correction_id'not in r for r in corrections['corrections'][:9])
assert [r['correction_id']for r in corrections['corrections'][9:]]==list(range(10,53))
manifest=read(ROOT/'reports/full-coverage/checkpoint-25-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage' and len(manifest['proof_files'])==1156
protected={n:r['sha256']for n,r in manifest['proof_files'].items()}
protected.update(proposal['current31_assets_sha256'])
owners={'book/coverage/'+n+'.json':h for n,h in proposal['current5_installed25_owner_sha256'].items()}
assert len(owners)==5 and len(proposal['current31_assets_sha256'])==31
protected.update(owners)
for p,h in protected.items():assert H(ROOT/p)==h,p
original_refs={str(proposal_path):H(proposal_path),str(peer_path):H(peer_path),**peer['closed_evidence_sha256']}
alias_targets={}
for p,h in original_refs.items():
 f=Path(p);assert f.is_absolute()and f.is_file()and not f.is_symlink()
 assert f.is_relative_to(ROOT)or f.parent==Path('/tmp')
 assert H(f)==h
 target=('semantic-original-root/'+f.relative_to(ROOT).as_posix())if f.is_relative_to(ROOT)else('semantic-original-tmp/'+f.name)
 if Path(target).suffix=='.txt':target+='.log'
 assert target not in alias_targets or alias_targets[target]==h
 alias_targets[target]=h
source=ROOT/proposal['source'];assert H(source)==proposal['source_sha256_before']
before=source.read_text()
def replace_all(body):
 for row in proposal['replacements']:
  assert type(row['count'])is int and row['count']==1 and body.count(row['before'])==1
  assert row['after']not in body
  body=body.replace(row['before'],row['after'],1)
 return body
after=replace_all(before)
assert hashlib.sha256(after.encode()).hexdigest()==proposal['proposed_source_sha256_after']
reverse=after
for row in reversed(proposal['replacements']):
 assert reverse.count(row['after'])==1;reverse=reverse.replace(row['after'],row['before'],1)
assert reverse==before and after.count('\n')==before.count('\n')
fixtures=[]
for name,body in [('duplicate_original_snippet',before+proposal['replacements'][0]['before']),('already_inserted_replacement',before+proposal['replacements'][0]['after'])]:
 try:replace_all(body)
 except AssertionError:fixtures.append({'fixture':name,'rejected':True})
 else:raise AssertionError(name)
inventory_path=ROOT/'book/coverage/inventory.json'
assert H(inventory_path)==H(ROOT/'book/coverage/inventory-after-correction52.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
old=read(inventory_path);parser=ROOT/'book/inventory_claims.py'
assert H(parser)=='b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
with tempfile.TemporaryDirectory(prefix='applied-source53-writer-peer-full29-')as tmp:
 isolated=Path(tmp);(isolated/'SafeLearning').mkdir()
 for page in(ROOT/'SafeLearning').glob('*.html'):
  if page==source:(isolated/'SafeLearning'/page.name).write_text(after)
  else:(isolated/'SafeLearning'/page.name).symlink_to(page)
 sys.path.insert(0,str(ROOT/'book'))
 spec=importlib.util.spec_from_file_location('independent_applied_source53_full29',parser)
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 module.ROOT=isolated;module.OUT=isolated/'book/coverage'
 with contextlib.redirect_stdout(io.StringIO()):module.inventory()
 new=read(module.OUT/'inventory.json')
assert new['counts']==old['counts']and new['counts']['exercises']==556 and new['counts']['material_source_units']==12774
assert len(new['source_sha256'])==29
assert new['source_sha256']=={**old['source_sha256'],proposal['source']:proposal['proposed_source_sha256_after']}
changed={}
for field in['exercises','material_source_units']:
 a={r['key']:r for r in old[field]};b={r['key']:r for r in new[field]};assert a.keys()==b.keys()
 changed[field]=[]
 for key in a:
  x,y=dict(a[key]),dict(b[key])
  if x['source']==proposal['source']:
   assert y['source_sha256']==proposal['proposed_source_sha256_after'];x.pop('source_sha256');y.pop('source_sha256')
  if x!=y:
   assert {k:v for k,v in x.items()if k not in['source_text','text_sha256']}=={k:v for k,v in y.items()if k not in['source_text','text_sha256']}
   changed[field].append(key)
 assert changed[field]==proposal['exact_changed_text_keys'][field]
for p,h in protected.items():assert H(ROOT/p)==h,p
assert H(inventory_path)=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
out=ROOT/'book/coverage/checks/future26-core/source53/source53-writer-v2-independent-applied-full-code-review-v1.json'
assert not out.exists();out.parent.mkdir(parents=True,exist_ok=True)
report={'status':'passed_independent_unexecuted_source53_writer_v2_full_code_and_isolated_parser_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next','helper':ref(helper),'helper_sha256':H(helper),'entire_reviewed_helper_body':text,'original_unexecuted_v1':{'helper':ref(old_helper),'entire_original_body':old_helper.read_text(),'scope':'Root read-only preflight found the legacy first-nine correction rows lack correction_id. No actual v1 writer execution or approval failure is inferred.'},'delta':'Only the historical correction-ID guard changes to exact current material-corrections hash, first-nine absence and exact10..52 IDs; inverse exactly recovers unexecuted v1.','proposal':ref(proposal_path),'entire_original_proposal_body_and_time':proposal,'independent_semantic_peer':ref(peer_path),'entire_original_semantic_peer_body_and_time':peer,'direct_mutable_targets':mutable,'new_history_and_output_scope':'write_new uses exclusive creation for source52/owner25 originals, exact semantic aliases, inventory-before/after53 and native record. Source53 changes only source page/current inventory/corrections; it never rewrites proof sources, owners, frozen outputs or old reviews.','future_delivery_gates':'All actual content+metadata push/live wrappers must be integer0 with original raw-log hashes, exact publication status, actual Pages/remote/HEAD commit equality, all31 HTTP200/matched immutable asset hashes. These are unexecuted future prerequisites at this code-review scope.','fresh_independent_full29_parser':{'parser':ref(parser),'changed_text_keys':changed,'counts':new['counts'],'all_other_keys_lines_DOM_and_text_records_preserved':True,'replacement_reverse_exact':True,'original_newline_count_preserved':True},'meaningful_replacement_reject_fixtures':fixtures,'archive_schema_validation':{'closed_original_count':len(original_refs),'no_symlink_or_unsupported_original':True,'canonical_destination_collisions_rejected':True},'protected_selected25_proofs':1156,'current_assets':31,'installed25_owners':5,'code_only':True,'preserved_initial_independent_reader_failure':{'checker':ref('/tmp/check-root-source53-writer-v2-independent-applied-v1.py'),'actual_record':ref('/tmp/root-source53-writer-v2-independent-applied-actual-v1.json'),'raw_log':ref('/tmp/root-source53-writer-v2-independent-applied-actual-v1.log'),'runner':ref('/tmp/run-root-source53-writer-v2-independent-applied-v1.py'),'entire_actual_record_and_time':read('/tmp/root-source53-writer-v2-independent-applied-actual-v1.json'),'reason':'Initial AST reader expected every write receiver to be a simple variable; the existing isolated parser write uses a temporary path expression. Corrected reader separately requires that expression to be the isolated SafeLearning tree; Root producer bytes remain exact.'},'actual_producer_execution_or_source53_application_claimed':False}
out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'review':ref(out),'helper_sha256':H(helper),'changed_text_keys':changed,'code_only':True}))
