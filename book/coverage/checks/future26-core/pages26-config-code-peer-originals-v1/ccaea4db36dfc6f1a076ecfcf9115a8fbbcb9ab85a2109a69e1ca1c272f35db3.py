"""Read-only independent code review and isolated fixtures; never executes Pages26 producer."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,subprocess
ROOT=Path('/home/oxrexkevin/SafetyBased');PUB=ROOT/'reports/book/publication-repo'
HELP='book/coverage/checks/root_prepare_pages26_config_v1.py';HS='b482976580808d3c4114d34bc97c585144ab70fa592335badaf999a5cf6e331b'
OUT=Path('/tmp/pages26-config-helper-independent-foundations-observation-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(n):return {'file':n,'sha256':sha(ROOT/n)}
assert sha(ROOT/HELP)==HS
body=(ROOT/HELP).read_text();tree=ast.parse(body);compile(tree,HELP,'exec')
# Evaluate only constant assignments and definitions; all production statements are excluded.
constants={}
for n in tree.body:
 if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
  try:constants[n.targets[0].id]=ast.literal_eval(n.value)
  except (ValueError,TypeError):pass
assert constants['BEFORE']=='7cbf6c4a7aa5c2f349b83025018e6a27898e567e1822f3aeab4d064fbfecb0af'
assert constants['BASE_MANIFEST_SHA']=='0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363'
assert constants['RETIRED_DIR']=='reports/full-coverage/lean-checkpoint-24'
assert constants['RETIRED_FILES']=={'reports/full-coverage/checkpoint-24-manifest.json':'5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0','reports/full-coverage/checkpoint-24-selection.json':'9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314'}
added=set(constants['RETIRED_FILES'])|{constants['RETIRED_DIR']}|constants['NEW_DUPLICATE_OR_SNAPSHOT_EXCLUSIONS']
assert added=={'reports/full-coverage/lean-checkpoint-24','reports/full-coverage/checkpoint-24-manifest.json','reports/full-coverage/checkpoint-24-selection.json','book/coverage/inventory-after-correction53.json','book/coverage/inventory-before-correction53.json','reports/full-coverage/checkpoint-26','reports/full-coverage/owner25-originals-before-owner26-integration-v1'}
old=(PUB/'_config.yml').read_bytes();assert sha(PUB/'_config.yml')==constants['BEFORE']
header='# Keep complete audit archives in Git while limiting the published website.\nexclude:\n'
exclusions={l[4:] for l in old.decode().splitlines() if l.startswith('  - ')}
assert len(exclusions)==101 and old.decode()==header+''.join('  - '+n+'\n' for n in sorted(exclusions)) and not added&exclusions
exclusions|=added;assert len(exclusions)==108
assert all(n and not Path(n).is_absolute() and '..' not in Path(n).parts and not any(c in n for c in '*?[{') for n in exclusions)
fnnodes=[n for n in tree.body if isinstance(n,ast.FunctionDef)]
ns={'Path':Path,'hashlib':hashlib,'json':json,'subprocess':subprocess,'ROOT':ROOT,'PUB':PUB,'exclusions':exclusions}
exec(compile(ast.Module(body=fnnodes,type_ignores=[]),HELP,'exec'),ns)
fixtures=[]
def test(label,fn):
 fn();fixtures.append(label)
def rejects(label,fn):
 try:fn()
 except (AssertionError,subprocess.CalledProcessError):fixtures.append(label);return
 raise AssertionError('fixture unexpectedly accepted: '+label)
for d in [{'actual_exit_code':0},{'exit_code':0},{'actual_exit_code':0,'exit_code':0}]:test('strict-exit accepts '+str(d),lambda d=d:ns['zero'](d))
for d in [{},{'exit_code':False},{'actual_exit_code':False},{'actual_exit_code':0,'exit_code':1},{'actual_exit_code':0,'exit_code':False},{'actual_exit_code':0.0},{'exit_code':'0'},{'actual_exit_code':1},{'actual_exit_code':-1}]:rejects('strict-exit rejects '+str(d),lambda d=d:ns['zero'](d))
required=['SafeLearning/'+p.name for p in (ROOT/'SafeLearning').iterdir() if p.is_file()]
required+=['book/coverage/'+o+'.json' for o in ('core','foundations','applied','modules')]
required+=['book/coverage/inventory.json','book/coverage/material-corrections.json','reports/full-coverage/integration-26.json','reports/full-coverage/browser-checkpoint-26.json','reports/full-coverage/checkpoint-26-manifest.json','reports/full-coverage/checkpoint-26-selection.json','reports/full-coverage/lean-checkpoint-26/verification-original.json','reports/full-coverage/lean-checkpoint-26/verification.json','reports/full-coverage/lean-checkpoint-26/ledger-audit.json','reports/full-coverage/checkpoint-25-manifest.json','reports/full-coverage/checkpoint-25-selection.json','reports/full-coverage/lean-checkpoint-25/verification-original.json']
assert len([n for n in required if n.startswith('SafeLearning/')])==31
for n in required:assert ns['kept'](n),n
fixtures.append('all31 assets/four owners/current26 and baseline25 required paths remain included')
for n in added:
 assert not ns['kept'](n) and not ns['kept'](n+'/test.json') and ns['kept'](n+'-different')
fixtures.append('seven literal exclusions preserve similarly prefixed sibling paths')
# Real old24 archival bytes only: ROOT/PUB/tracked HEAD exact before any future mutation.
retired={p.relative_to(ROOT).as_posix():sha(p) for p in (ROOT/constants['RETIRED_DIR']).rglob('*') if p.is_file()}
assert retired and constants['RETIRED_DIR']+'/verification-original.json' in retired
assert {p.relative_to(PUB).as_posix():sha(p) for p in (PUB/constants['RETIRED_DIR']).rglob('*') if p.is_file()}==retired
ns['tracked_exact'](constants['RETIRED_DIR'],retired);fixtures.append('actual retired24 archive exact ROOT/PUB/tracked HEAD')
for n,h in constants['RETIRED_FILES'].items():
 ns['tracked_exact'](n,{n:h});fixtures.append('actual retired24 direct archive exact '+n)
# Isolated mismatches to the native tracked_exact guard, without editing any file.
n,h=next(iter(constants['RETIRED_FILES'].items()))
rejects('tracked-set mismatch rejected',lambda:ns['tracked_exact'](n,{n+'-unexpected':h}))
rejects('retired-byte wrong digest rejected',lambda:ns['tracked_exact'](n,{n:'0'*64}))
# Inspect exact production assertion structure, pre-write ordering and future audit predicates.
asserts=[n for n in ast.walk(tree) if isinstance(n,ast.Assert)]
asserttext='\n'.join(ast.unparse(n.test) for n in asserts)
for clause in ["selection['new_file_count'] == 11","audit['theorem_count'] == 9503","len(audit['declarations']) == len(audit['axiom_dependencies']) == 9503","len(assets) == 31","len(exclusions) == 108","included < 850000000","normalized == json.loads((PUB / n).read_text())"]:
 assert clause in asserttext,clause
assert 'fresh_kernel_replay' in asserttext and 'reused_identical_module_and_transitive_local_imports' in asserttext and '1156' in asserttext
writes=[n.lineno for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in {'write_bytes','open'} and ((n.func.attr=='write_bytes') or (n.args and isinstance(n.args[0],ast.Constant) and n.args[0].value=='xb'))]
assert writes and max(n.lineno for n in asserts if ast.unparse(n.test)=='included < 850000000')<min(writes)
assert all(line>next(n.lineno for n in asserts if "normalized == json.loads" in ast.unparse(n.test)) for line in writes)
fixtures.append('actual audit/status/pruning/archival/budget guards all precede native and config writes')
# Genuine old25 ledger schema exercises the same exact three-row removal scopes read-only.
man=json.loads((ROOT/'reports/full-coverage/checkpoint-25-manifest.json').read_text())
assert sha(ROOT/'reports/full-coverage/checkpoint-25-manifest.json')==constants['BASE_MANIFEST_SHA']
for owner in ('core','foundations','applied','modules'):
 live=json.loads((ROOT/('book/coverage/'+owner+'.json')).read_text());snapshot=json.loads((ROOT/man['snapshot']/('book/coverage/'+owner+'.json')).read_text());removed=man['excluded_unreferenced_ledger_metadata'][owner]
 assert len(removed)==(3 if owner=='applied' else 0)
 normalized=copy.deepcopy(live)
 for source in removed:assert source in normalized['proof_files'] and source not in man['proof_files'];normalized['proof_files'].pop(source)
 assert normalized==snapshot
 fixtures.append('real held25 '+owner+' full JSON normalization scope exact')
# Negative normalization fixtures retain arbitrary body or selected-metadata edits as differences.
original={'proof_files':{'unused1':'a','unused2':'b','unused3':'c','selected':'d'},'original_review':{'time':'exact','body':[1,2]}}
expected={'proof_files':{'selected':'d'},'original_review':{'time':'exact','body':[1,2]}}
normalized=copy.deepcopy(original)
for key in ('unused1','unused2','unused3'):normalized['proof_files'].pop(key)
assert normalized==expected;fixtures.append('synthetic only three declared unselected metadata rows normalize')
for altered in [dict(expected,original_review={'time':'changed','body':[1,2]}),dict(expected,original_review={'time':'exact','body':[1,3]}),dict(expected,proof_files={}),dict(expected,proof_files={'selected':'wrong'})]:
 assert altered!=normalized;fixtures.append('synthetic whole JSON rejects undeclared body/time/selected-source modification')
prospective_current_tree=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and ns['kept'](p.relative_to(PUB).as_posix()))-len(old)+len((header+''.join('  - '+n+'\n' for n in sorted(exclusions))).encode())
assert sha(ROOT/HELP)==HS and sha(PUB/'_config.yml')==constants['BEFORE']
report={'status':'independent_pages26_configuration_helper_code_and_read_only_fixtures_passed','errors':[],'reviewer':'independent_foundations_agent','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELP),'helper_sha256':HS,'fixture_count':len(fixtures),'fixture_results':fixtures,'baseline_configuration_sha256':constants['BEFORE'],'retained_literal_exclusion_count':101,'new_exact_literal_exclusions':sorted(added),'final_literal_exclusion_count':108,'all31_assets_current26_baseline25_and_four_owners_kept_by_literal_rules':True,'retired_archive_files_verified_exact_root_pub_tracked_HEAD':len(retired)+2,'retired_older_archival_bytes':sum((ROOT/n).stat().st_size for n in retired)+sum((ROOT/n).stat().st_size for n in constants['RETIRED_FILES']),'readonly_current_pub_tree_prospective_bytes_with_draft_literal_rules':prospective_current_tree,'website_budget_bytes':850000000,'actual26_preparation_executed':False,'actual26_audit_publication_readiness_or_budget_pass_claimed':False,'scope':'Full draft code review plus strict exit, literal boundaries, native pre-write ordering, real retired24 ROOT/PUB/HEAD bytes and genuine held25 pruning schemas. Actual26 audit/selection/frozen owner/current53 publication and final native/staging bytes remain future prerequisites; current-tree byte observation is not the future prepared26 budget.'}
assert not OUT.exists();OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':'passed','observation':str(OUT),'sha256':sha(OUT),'fixture_count':len(fixtures)}))
