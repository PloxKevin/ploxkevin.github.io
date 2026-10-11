from pathlib import Path
from datetime import datetime,timezone
from types import SimpleNamespace
import ast,json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');P=R/'book/coverage/checks/root_finalize_core27_current55_v2.py';OLD=R/'book/coverage/checks/root_finalize_core27_current55_v1.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ref=lambda p:{'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p)}
assert sha(P)=='684a03bd85a0664faf7c3cef41a6dfd128b35e4ac20e82bb045b0006c284271e'
src=P.read_text();old=OLD.read_text();tree=ast.parse(src);oldtree=ast.parse(old)
assert "assert peer['candidate']==ready['candidate'] and peer['readiness']==ref(READY)" in src
assert "assert r['source_snapshot']['sha256']==SOURCE_SHA" in src
assert "for n,h in sorted(peer_closure.items()):" in src
assert "peer_closure=peer['closed_evidence_sha256']" in src and "len(peer_closure)==13" in src
# Exact documented delta: three guards and raw-copy closure; all other lines are preserved.
reverted=src.replace("assert peer['candidate']==ready['candidate'] and peer['readiness']==ref(READY)\npeer_closure=peer['closed_evidence_sha256']\nassert isinstance(peer_closure,dict) and len(peer_closure)==13\nfor n,h in peer_closure.items():checked({'file':n,'sha256':h})","assert ready['candidate']['sha256'] in peer_path.read_text() and READY_SHA in peer_path.read_text()")
reverted=reverted.replace(";assert r['source_snapshot']['sha256']==SOURCE_SHA","").replace("for n,h in sorted(peer_closure.items()):\n p=checked({'file':n,'sha256':h});t=BASE/'original-peer'/p.name;copy_new(p,t);closed[n]=ref(t)\n","")
assert reverted==old
prefix=[]
for node in tree.body:
 if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='parser' for t in node.targets):continue
 if isinstance(node,ast.Expr) and isinstance(node.value,ast.Call) and isinstance(node.value.func,ast.Attribute) and isinstance(node.value.func.value,ast.Name) and node.value.func.value.id=='BASE' and node.value.func.attr=='mkdir':break
 prefix.append(node)
module=ast.fix_missing_locations(ast.Module(body=prefix,type_ignores=[]));ns={'__file__':str(P),'args':SimpleNamespace(draft_peer='/tmp/core27-current55-eleven-component-draft-independent-foundations-mechanics-review-v1.json',draft_peer_sha256='02c5bbce03c7df04ba3d34c0ce0aed023fc7255b9858b8f4a1900043247dd262')}
exec(compile(module,str(P),'exec'),ns)
assert not ns['BASE'].exists();assert len(ns['new_claims'])==44
new=ns['new'];draft=ns['draft'];inverse=copy.deepcopy(new);inverse.pop('future27_component_pair_binding');inverse['proof_files']=copy.deepcopy(draft['proof_files']);inverse['counts']['proof_files']=181
for row in inverse['material_claims']+[c for e in inverse['exercises'] for c in e['claims']]:
 if 'core27-mpc-precise-component-' in row['id']:
  original=next(r for r in draft['material_claims']+[c for e in draft['exercises'] for c in e['claims']] if r['id']==row['id']);row['independent_review']=copy.deepcopy(original['independent_review'])
assert inverse==draft
assert len(ns['rows'])==2 and len(ns['peer_closure'])==13
peer=ns['peer'];ready=ns['ready'];aliases=ns['aliases']
# Execute the exact corrected assertions on isolated JSON clones, never synthetic actual records on disk.
peer_guard=compile(ast.parse("assert peer['candidate']==ready['candidate'] and peer['readiness']==ref(READY)"),'<exact-peer-guard>','exec')
snapshot_guard=compile(ast.parse("assert r['source_snapshot']['sha256']==SOURCE_SHA"),'<exact-snapshot-guard>','exec')
def accept(code,ctx):exec(code,ctx)
def reject(code,ctx):
 try:exec(code,ctx)
 except (AssertionError,KeyError,TypeError):return
 raise AssertionError('invalid fixture accepted')
fixtures=0
accept(peer_guard,dict(ns));fixtures+=1
for field in ('candidate','readiness'):
 for alteration in ('hash','file','missing','list'):
  q=copy.deepcopy(peer)
  if alteration=='hash':q[field]['sha256']='0'*64
  elif alteration=='file':q[field]['file']='/tmp/unrelated.json'
  elif alteration=='missing':q.pop(field)
  else:q[field]=[q[field]]
  q['unrelated_original_text_contains_correct_hashes']=ready['candidate']['sha256']+ns['READY_SHA'];reject(peer_guard,dict(ns,peer=q));fixtures+=1
for row in ns['rows']:
 accept(snapshot_guard,dict(ns,r=row));fixtures+=1
 q=copy.deepcopy(row);q['source_snapshot']['sha256']='0'*64;reject(snapshot_guard,dict(ns,r=q));fixtures+=1
for d in ({'exit_code':0},{'actual_exit_code':0,'exit_code':0}):ns['zero'](d);fixtures+=1
for d in ({},{'exit_code':False},{'actual_exit_code':0.0},{'exit_code':0,'actual_exit_code':1},{'exit_code':'0'},{'exit_code':-1}):
 try:ns['zero'](d)
 except AssertionError:pass
 else:raise AssertionError('invalid exit accepted')
 fixtures+=1
# Exact original aliases cannot be replaced with current bytes or arbitrary digests.
for r in ready['original_full_component_peers']:
 a=ns['alias'](r['file'],r['sha256']);body=json.loads(ns['checked'](a).read_bytes());assert body==r['entire_original_body_and_time'];fixtures+=1
 try:ns['alias'](r['file'],'0'*64)
 except (AssertionError,KeyError):pass
 else:raise AssertionError('invalid alias accepted')
 fixtures+=1
# Every peer-history basename is unique; no overwrite collision in the new raw-copy archive.
paths=[Path(n).name for n in ns['peer_closure']]+[ns['peer_path'].name];assert len(paths)==len(set(paths));assert all(Path(n).is_file() for n in ns['peer_closure'])
# Prepare-loop body reaches its first write only after these genuine guards; producer never invoked.
assert not ns['BASE'].exists()
out=Path('/tmp/core27-finalizer2-independent-foundations-check-result-v1.json');assert not out.exists()
d={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; Root authored Core finalizer','helper':ref(P),'helper_sha256':sha(P),'preserved_original_unexecuted_helper':ref(OLD),'original_draft_mechanics_peer':ref(ns['peer_path']),'entire_original_draft_mechanics_peer_body_and_time':peer,'native_preflight':{'actual_combined_readiness':ref(R/ns['PAIRS']),'actual_combined_execution':ref(R/ns['ACTUAL']),'canonical_core_records':2,'old_proof_metadata':181,'new_export_count':11,'source_snapshot_matches_exact_original':True,'normalized_review_references':44,'peer_closed_history_files':13,'full_pair_binding_inverse_restores_draft':True,'whole_MPC_exercise_and_three_source_units_pending':True},'focused_fixture_count':fixtures,'producer_invoked':False,'first_archive_or_candidate_write_reached':False,'scope':'Entire new helper read, exact v2 delta inverse, genuine native preflight only and isolated reject fixtures. All original source/review bodies and times retain their scope. No compiler, archive, candidate, live owner, source, Git or publication mutation.'};out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'status':'passed','fixtures':fixtures,'native_pair_records':2,'peer_histories':13,'writes':0}))
