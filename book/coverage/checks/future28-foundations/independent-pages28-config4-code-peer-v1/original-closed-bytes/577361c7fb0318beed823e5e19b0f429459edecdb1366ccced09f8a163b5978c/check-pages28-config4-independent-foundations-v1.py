from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,tempfile
R=Path('/home/oxrexkevin/SafetyBased');S=R/'book/coverage/checks/root_prepare_pages28_config_v4.py';OUT=Path('/tmp/pages28-config4-independent-foundations-findings-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def j(p):return json.loads(p.read_bytes())
def ref(p):return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p)}
assert sha(S)=='2609794894022803a89b9d618e65dd367ba35a1c18972ee184ec8c131237f0d4' and not OUT.exists()
started=datetime.now(timezone.utc).isoformat();old=(R/'book/coverage/checks/root_prepare_pages28_config_v3.py').read_text();new=S.read_text()
replacement=" archival={n:r['sha256'] for n,r in selection['proof_files'].items()}\n assert 'verification/lean' in old and len(archival)==1186\n for n,h in archival.items():\n  assert n.startswith('verification/lean/SafeLearning/') and sha(ROOT,n)==sha(PUB,n)==h"
rest=new.replace("SELF='book/coverage/checks/root_prepare_pages28_config_v4.py'","SELF='book/coverage/checks/root_prepare_pages28_config_v3.py'").replace(replacement," for n,r in selection['proof_files'].items():required[n]=r['sha256']").replace("'exact_selected_lean_sources_in_git_archive_sha256':archival,",'').replace('all1186 selected Lean sources remain exact in the Git archive under the unchanged verification/lean website exclusion. The9896 theorem audit,current ledgers,source60 assets and48 screenshot downloads remain hosted.','current1186 selected sources,9896 theorem audit,current ledgers, source60 assets and48 screenshot downloads remain hosted.')
assert rest==old
spec=importlib.util.spec_from_file_location('pages4_code_only',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
tree=ast.parse(new);prep=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='prepare');start=next(i for i,x in enumerate(prep.body) if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='archival' for t in x.targets));nodes=prep.body[start:start+3];assert isinstance(nodes[1],ast.Assert) and isinstance(nodes[2],ast.For)
code=compile(ast.Module(body=nodes,type_ignores=[]),'<exact-pages4-archival-membership-block>','exec');obs=[{'fixture':'exact_full3_to4_delta_only_self_archival_guard_report_field_scope','passed':True}]
selection=j(R/'reports/full-coverage/checkpoint-28-selection.json');config=R/'reports/book/publication-repo/_config.yml';original=config.read_bytes();oldex={line[4:] for line in original.decode().splitlines() if line.startswith('  - ')}
assert 'verification/lean' in oldex and len(oldex)==133 and sha(config)==m.BEFORE
env={'selection':selection,'old':oldex,'ROOT':R,'PUB':m.PUB,'sha':m.sha};exec(code,env)
assert len(env['archival'])==1186 and env['archival']=={n:r['sha256'] for n,r in selection['proof_files'].items()}
assert all(not m.kept(n,oldex|m.ADDITIONS) for n in env['archival'])
obs.append({'fixture':'all1186_real_current_selected_root_pub_sha_equal_with_existing_exclusion','passed':True})
previous=R/'reports/full-coverage/pages28-config-preflight-execution-v1.json';failure=j(previous)
assert type(failure['actual_exit_code']) is int and failure['actual_exit_code']==1
obs.append({'fixture':'original_genuine_root_v3_prewrite1_preserved_separate_from_code_reader','passed':True})
def reject(label,e):
 try:exec(code,e)
 except (AssertionError,KeyError,ValueError):obs.append({'fixture':label,'rejected':True})
 else:raise AssertionError(label)
with tempfile.TemporaryDirectory(prefix='pages4-archival-') as td:
 base=Path(td);a=base/'root';b=base/'pub';prefix='verification/lean/SafeLearning/';fixture={'proof_files':{prefix+'Fixture'+str(i)+'.lean':{'sha256':hashlib.sha256(b'exact').hexdigest()} for i in range(1186)}}
 for root in [a,b]:
  (root/prefix).mkdir(parents=True)
  for n in fixture['proof_files']:(root/n).write_bytes(b'exact')
 def e(sel=fixture,excluded={'verification/lean'}):return {'selection':sel,'old':excluded,'ROOT':a,'PUB':b,'sha':m.sha}
 exec(code,e());obs.append({'fixture':'isolated_valid1186_exact_archival_source_files','passed':True})
 reject('missing_existing_literal_lean_exclusion',e(excluded=set()))
 reject('different_similar_exclusion_is_not_exact',e(excluded={'verification/leans'}))
 bad=copy.deepcopy(fixture);bad['proof_files'].pop(next(iter(bad['proof_files'])));reject('missing_selected_source',e(bad))
 bad=copy.deepcopy(fixture);bad['proof_files'][prefix+'extra.lean']={'sha256':'0'*64};reject('unexpected_selected_source_count',e(bad))
 n=next(iter(fixture['proof_files']));bad=copy.deepcopy(fixture);bad['proof_files'][n]['sha256']='0'*64;reject('wrong_expected_selected_sha',e(bad))
 bad=copy.deepcopy(fixture);bad['proof_files'][n]['sha256']=False;reject('boolean_selected_sha',e(bad))
 for wrong in ['SafeLearning/book.html','verification/lean/Other.lean','/tmp/escape.lean',prefix+'../Escape.lean']:
  bad=copy.deepcopy(fixture);bad['proof_files'][wrong]=bad['proof_files'].pop(n);reject('invalid_archival_source_'+wrong,e(bad))
 (a/n).write_bytes(b'changed');reject('changed_root_source_bytes',e());(a/n).write_bytes(b'exact')
 (b/n).write_bytes(b'changed');reject('changed_publication_archive_source_bytes',e());(b/n).write_bytes(b'exact')
 (b/n).unlink();(b/n).symlink_to(a/n);reject('selected_archive_source_symlink',e())
 assert m.kept('reports/full-coverage/lean-checkpoint-28/verification-original.json',oldex|m.ADDITIONS)
 assert m.kept('reports/full-coverage/browser-artifacts-28/capture.png',oldex|m.ADDITIONS)
 assert m.kept('book/coverage/foundations.json',oldex|m.ADDITIONS)
 assert m.kept('SafeLearning/primer-basics.html',oldex|m.ADDITIONS)
 obs.append({'fixture':'current_audit_images_ledgers_and_source_assets_still_website_members','passed':True})
assert config.read_bytes()==original
d={'status':'passed_full_independent_pages28_config4_archival_delta_and_native_membership_review','errors':[],'reviewer':'/root/foundations_recovery28','reader_started_at_utc':started,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(S),'previous_full_code_peer':ref(R/'book/coverage/checks/future28-foundations/independent-pages28-config3-code-peer-v1/pages28-config3-independent-foundations-closed-v1.json'),'full_source_lines_read':len(new.splitlines()),'fixture_count':len(obs),'fixture_observations':obs,'current_selected_archival_sources_count':1186,'archival_sources_canonical_map_sha256':hashlib.sha256(json.dumps(env['archival'],sort_keys=True,separators=(',',':')).encode()).hexdigest(),'original_root_prewrite_failure':ref(previous),'code_approval_for_root_owned_genuine_runtime_preflight':True,'producer_prepare_or_writer_executed':False,'actual_complete_production_budget_preflight_claimed':False,'production_delivery_approval':False,'scope':'All1186 real ROOT/PUB archive sources match selection. Website membership excludes Lean tree under existing literal rule;9896 theorem audit/current ledgers/source31/images remain required. Prior full3 code/native/78 observations unchanged; current4 exact guard fixtures do not substitute for Root genuine prepare/budget/Git/Pages/live commands.'}
OUT.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({'findings':ref(OUT),'fixture_count':len(obs),'code_approval':True,'producer_executed':False}))
