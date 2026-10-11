"""Read-only helper code review and explicitly isolated schema fixtures.
No Root integration main, dry/apply, owner copying or candidate release occurs.
"""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-core'
HELPER=ROOT/'book/coverage/checks/root_integrate_owner24_candidates_v2.py'
OLD=ROOT/'book/coverage/checks/root_integrate_owner24_candidates_v1.py'
OUT=BASE/'owner24-integration-helper-independent-foundations-code-review-v1.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
ref=lambda p:{'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
assert not OUT.exists() and H(HELPER)=='07980ea65f4f983e832d761579e68fa0000c362aa8a8ffb9c2b8800bf6dd2489'
assert H(OLD)=='8d10b16ed928b6c622fddcfb1ff1b5b9391d60721664bb698c75be9343e0047a'
t=ast.parse(HELPER.read_text());old=ast.parse(OLD.read_text())
def topfor(tree):return next(n for n in tree.body if isinstance(n,ast.For) and ast.unparse(n.target)=='owner')
def proofloop(tree):return next(n for n in topfor(tree).body if isinstance(n,ast.For) and ast.unparse(n.target)=='(name, proof)')
def pairloop(tree):return next(n for n in proofloop(tree).body if isinstance(n,ast.For) and ast.unparse(n.target)=='ref')
op,np=pairloop(old),pairloop(t)
oldcommand=next(i for i,n in enumerate(op.body) if isinstance(n,ast.Assert) and 'execution[\'command\']' in ast.unparse(n))
newcommand=next(i for i,n in enumerate(np.body) if isinstance(n,ast.Assign) and ast.unparse(n.targets[0])=='commands')
assert oldcommand==newcommand
norm=copy.deepcopy(old);pairloop(norm).body[oldcommand:oldcommand+1]=copy.deepcopy(np.body[newcommand:newcommand+2])
assert ast.dump(norm)==ast.dump(t),'v1/v2 changes beyond precise command alias validation'
defs=[n for n in t.body if isinstance(n,ast.FunctionDef) and n.name in ['safe_path','sha','read','reference','pointer']]
ns={'ROOT':ROOT,'Path':Path,'hashlib':hashlib,'json':json};exec(compile(ast.Module(body=defs,type_ignores=[]),str(HELPER),'exec'),ns)
fixtures=[]
def reject(label,f):
 try:f()
 except (AssertionError,KeyError):fixtures.append('reject_'+label)
 else:raise AssertionError(label+' accepted')
assert ns['safe_path']('book/coverage/foundations.json')==ROOT/'book/coverage/foundations.json'
reject('absolute_input_path',lambda:ns['safe_path']('/tmp/other'))
reject('parent_traversal',lambda:ns['safe_path']('../other'))
manifestp=ROOT/'reports/full-coverage/checkpoint-23-manifest.json';manifest=read(manifestp)
assert H(manifestp)=='e21eac7bfafd8002d75966240e5c3ea940ebec3dba4066fb1e9a767627d7fb06'
assert len(manifest['proof_files'])==1131 and len(manifest['frozen_inputs_sha256'])==36910
assert ns['reference'](ref(manifestp))==manifest
reject('reference_digest_changed',lambda:ns['reference']({'file':str(manifestp.relative_to(ROOT)),'sha256':'0'*64}))
held={n:manifest['working_inputs_sha256'][n] for n in ['book/coverage/'+s+'.json' for s in ['core','foundations','applied','modules','applied-promotions']]}
for n,h in held.items():assert H(ROOT/n)==h
# Actual immutable paired records exercise the literal helper block. Only the
# command/exits mutation fixtures below are synthetic copies, never real runs.
offerp=ROOT/'book/coverage/checks/foundations-future24/source51/foundations-audit24-candidate-source51-additions-v1-reviewed.json';offer=read(offerp)
assert H(offerp)=='c939f72d7ed32eb76016788ce8c0aabcf244c2334753a2f9564b08cfc3168b26'
def runpair(recordp,mutator=None):
 actual=read(recordp);execution=copy.deepcopy(actual)
 if mutator:mutator(execution)
 command=actual.get('actual_command',actual.get('command'))
 r=dict(ref(recordp),actual_source=actual['source'],actual_command=command,actual_workdir=actual['actual_workdir'],canonical_raw_log={'file':actual['log'],'sha256':actual['log_sha256']})
 env={'ROOT':ROOT,'reference':lambda x:execution,'sha':ns['sha'],'ref':r,'name':actual['source'],
      'proof':{'sha256':actual['source_sha256_before']},'retained_reference_sha256':{}}
 exec(compile(ast.Module(body=np.body,type_ignores=[]),str(HELPER),'exec'),env)
 assert env['retained_reference_sha256'][r['file']]==r['sha256']
 return actual
actual_records=[]
for path,digest in offer['actual_canonical_execution_records_sha256'].items():
 p=ROOT/path;assert H(p)==digest
 r=runpair(p);actual_records.append(ref(p))
assert len(actual_records)==10
fixtures.append('accept_all10_genuine_Foundation24_actual_command_actual_exit_code_paired_records')
p=ROOT/next(iter(offer['actual_canonical_execution_records_sha256']))
runpair(p,lambda x:x.update(command=x['actual_command']))
fixtures.append('accept_equal_command_and_actual_command_aliases')
runpair(p,lambda x:x.update(command=x.pop('actual_command')))
fixtures.append('accept_sole_command_schema')
reject('conflicting_command_aliases',lambda:runpair(p,lambda x:x.update(command=['false'])))
reject('no_command_field',lambda:runpair(p,lambda x:x.pop('actual_command')))
reject('actual_nonzero_exit',lambda:runpair(p,lambda x:x.update(actual_exit_code=1)))
reject('conflicting_exit_aliases',lambda:runpair(p,lambda x:x.update(exit_code=1)))
reject('no_exit_field',lambda:runpair(p,lambda x:x.pop('actual_exit_code')))
reject('source_path_changed',lambda:runpair(p,lambda x:x.update(source='verification/lean/SafeLearning/other.lean')))
reject('source_after_digest_changed',lambda:runpair(p,lambda x:x.update(source_sha256_after='0'*64)))
reject('actual_workdir_changed',lambda:runpair(p,lambda x:x.update(actual_workdir='/tmp')))
reject('raw_log_digest_changed',lambda:runpair(p,lambda x:x.update(log_sha256='0'*64)))
# Execute the exact source52/asset gate with clearly synthetic future records.
# These fixtures prove guard behavior, and make no actual source52 result claim.
start=next(i for i,n in enumerate(t.body) if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='original23_assets' for x in n.targets))
end=next(i for i,n in enumerate(t.body) if isinstance(n,ast.FunctionDef) and n.name=='verify_frozen_and_sources')
assetcode=ast.Module(body=t.body[start:end],type_ignores=[])
oldassets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(oldassets)==31
futureassets=dict(oldassets,**{'SafeLearning/nn-in-the-loop.html':'1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041'})
def sourcegate(change=None):
 records={'fixture_apply':{'actual_exit_code':0,'log':'fixture_log','log_sha256':'a'*64},'fixture_post':{'actual_exit_code':0,'inventory_after_sha256':'b'*64}}
 binding={'exact_current52_safelearning_assets_sha256':copy.deepcopy(futureassets),'actual_source52_apply':'fixture_apply','actual_source52_postwrite':'fixture_post','source52_corrections_sha256':'c'*64}
 if change:change(binding,records)
 env={'assets':copy.deepcopy(oldassets),'binding':binding,'reference':lambda r:records[r],
      'INVENTORY_SHA':'b'*64,'sha':lambda p:'a'*64 if p=='fixture_log' else 'c'*64,
      'read':lambda p:{'corrections':[{}]*52}}
 exec(compile(assetcode,str(HELPER),'exec'),env)
sourcegate();fixtures.append('accept_synthetic_source52_actual0_matching_inventory_exact_single_NN_asset_delta')
reject('future_apply_exit1',lambda:sourcegate(lambda b,r:r['fixture_apply'].update(actual_exit_code=1)))
reject('future_postwrite_exit1',lambda:sourcegate(lambda b,r:r['fixture_post'].update(actual_exit_code=1)))
reject('postwrite_inventory_conflict',lambda:sourcegate(lambda b,r:r['fixture_post'].update(inventory_after_sha256='d'*64)))
reject('unexpected_second_asset_change',lambda:sourcegate(lambda b,r:b['exact_current52_safelearning_assets_sha256'].update({'SafeLearning/primer-basics.html':'0'*64})))
reject('wrong_NN_final_digest',lambda:sourcegate(lambda b,r:b['exact_current52_safelearning_assets_sha256'].update({'SafeLearning/nn-in-the-loop.html':'0'*64})))
reject('missing_asset',lambda:sourcegate(lambda b,r:b['exact_current52_safelearning_assets_sha256'].pop('SafeLearning/primer-basics.html')))
# Original semantic status/time must be exact; a blanket 'passed' interpretation
# is deliberately not used for genuine historical approved-component reports.
semanticloop=next(n for n in topfor(t).body if isinstance(n,ast.For) and ast.unparse(n.iter)=="row['original_full_source_semantic_reviews']")
def semantic_fixture(delta=None):
 original={'status':'independent_components_approved_whole_pending','checked_at_utc':'original-time','errors':[]}
 r={'file':'fixture','sha256':'e'*64,'original_review_status':original['status'],'original_review_time':original['checked_at_utc']}
 if delta:delta(original,r)
 env={'row':{'original_full_source_semantic_reviews':[r]},'reference':lambda x:original,'retained_reference_sha256':{}}
 exec(compile(ast.Module(body=[semanticloop],type_ignores=[]),str(HELPER),'exec'),env)
semantic_fixture();fixtures.append('accept_exact_historical_component_approved_whole_pending_status_without_retimming')
reject('semantic_status_reinterpreted',lambda:semantic_fixture(lambda o,r:r.update(original_review_status='passed')))
reject('semantic_time_replaced',lambda:semantic_fixture(lambda o,r:r.update(original_review_time='new-time')))
reject('semantic_errors_nonempty',lambda:semantic_fixture(lambda o,r:o.update(errors=['gap'])))
# Inspect copy mechanics: all binding/frozen/source/candidate/paired guards run
# before the only archive/copy block; only five whitelisted owner destinations.
apply=next(n for n in t.body if isinstance(n,ast.If) and ast.unparse(n.test)=='args.apply')
assert any(isinstance(n,ast.Expr) and ast.unparse(n)=='verify_frozen_and_sources()' for n in apply.body)
assert "os.replace(temporary, original)" in ast.unparse(apply)
assert "original23_byte_copy" in ast.unparse(apply)
assert "with preserved.open('xb')" in ast.unparse(apply) and "with temporary.open('xb')" in ast.unparse(apply)
assert "allowed_destinations = set(OWNERS.values()) | AUXILIARIES" in HELPER.read_text()
assert "assert set(row[\"destination\"] for row in replacements) <= allowed_destinations" in HELPER.read_text()
assert "args.apply" in ast.unparse(apply.test)
report={'status':'passed_independent_owner24_integration_helper_v2_code_and_focused_schema_fixtures',
 'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELPER),'helper_sha256':H(HELPER),
 'checker':ref(Path(__file__)),'original_unexecuted_v1':ref(OLD),'baseline23_manifest':ref(manifestp),
 'all_five_actual_live23_owner_sha256':held,'actual10_genuine_Foundation24_pair_refs_tested':actual_records,
 'explicit_accept_reject_fixtures':fixtures,'command_alias_delta_is_exact_only_v1_to_v2_code_change':True,
 'manual_full_helper_and_reviewed23_ancestor_delta_read':True,'four_owner_plus_only_Applied_promotions_copy_scope':True,
 'original_semantic_status_time_error_and_full_reference_hash_guards_retained':True,
 'frozen23_all36910_current_selected1131_source52_inventory_and31_asset_guards_before_and_after_copy':True,
 'final_four_owner_binding_manifest_reviewed_or_executed':False,'Root_integration_main_dry_apply_executed':False,'errors':[],
 'scope':'Code and isolated schema fixtures only. Exact real Foundation paired records were read, not rerun. Synthetic future source52 records demonstrate accept/reject guards and are explicitly not actual execution evidence. Root actual source52 apply, all four final source52 identity candidates/peers and binding manifest remain required before production guard/apply.'}
with OUT.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'review':ref(OUT),'helper_sha256':H(HELPER),'fixtures':len(fixtures),'integration_executed':False}))
