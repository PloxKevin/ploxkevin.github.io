from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/foundations-literal-partial7-full-review28-v2');assert not OUT.exists();OUT.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
def encoded(j):return (json.dumps(j,ensure_ascii=False,indent=2)+'\n').encode()
invp=ROOT/'book/coverage/inventory.json';ownerp=ROOT/'book/coverage/foundations.json'
assert sha(invp)=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
assert sha(ownerp)=='b3de5e813f882355cd90e46d27adc4ce56351ddd51d9038a1b8c79511b365b55'
inv=json.loads(invp.read_bytes());owner=json.loads(ownerp.read_bytes())
key='primer-optimization.html::node-186'
unit=next(u for u in inv['material_source_units']if u['key']==key)
assert hashlib.sha256(unit['source_text'].encode()).hexdigest()==unit['text_sha256']
html=ROOT/unit['source'];assert sha(html)==unit['source_sha256']
source=Path('/tmp/CompleteFoundationsLiteralPartialPitfall28-draft-v3.lean')
assert sha(source)=='5caaf0d58af8a86977b4fbca8195d534c10464ba1dfc6703ae4d1fb750b99a3c'
text=source.read_text();names=re.findall(r'^theorem (\w+)',text,re.M);assert len(names)==7
ns='SafeLearning.CompleteFoundationsLiteralPartialPitfall28.'
files=[source,html,Path(__file__),Path('/tmp/prepare-foundations-literal-partial7-full-review28-v1.py'),Path('/tmp/foundations-literal-partial7-packaging-failure1-observation.json'),Path('/tmp/foundations-literal-partial7-packaging-failure1-observed-tool-output.log')];records=[]
selection=json.loads((ROOT/'reports/full-coverage/checkpoint-27-selection.json').read_bytes())
for n,h in selection['proof_files'].items():assert sha(ROOT/n)==h,n
for n,h in inv['source_sha256'].items():assert sha(ROOT/n)==h,n
for n,want in ((1,1),(2,0),(3,0)):
    p=Path(f'/tmp/foundations-literal-partial-pitfall7-28-trial{n}.json');a=json.loads(p.read_bytes())
    assert type(a['actual_exit_code'])is int and a['actual_exit_code']==want
    assert type(a['actual_runner_exit_code'])is int and a['actual_runner_exit_code']==want
    assert a['protection_errors']==[] and a['source_unchanged']is True
    assert a['actual_command']==['lake','env','lean',a['source']] and a['actual_workdir']==str(ROOT/'verification/lean')
    assert sha(a['source'])==a['source_sha256_before']==a['source_sha256_after']==a['source_snapshot_sha256']==sha(a['source_snapshot'])
    assert sha(a['raw_log'])==a['raw_log_sha256']
    assert a['protected_selected27_proof_sources']==1175 and a['unchanged_current55_book_assets']==31 and a['unchanged_installed27_live_owners']==5
    for path,h in a['installed27_owner_sha256'].items():assert sha(ROOT/path)==h,path
    for path,h in a['pinned_installed27_provenance_sha256'].items():assert sha(ROOT/path)==h,path
    assert sha(a['original_actual_runner']['file'])==a['original_actual_runner']['sha256']
    log=Path(a['raw_log']).read_text();warnings=re.findall(r'^.+\.lean:\d+:\d+: warning:.*$',log,re.M)
    records.append({'record':ref(p),'entire_original_record_and_time':a,'entire_original_source':Path(a['source_snapshot']).read_text(),'entire_raw_log':log,'actual_emitted_warning_diagnostics':warnings})
    files.extend([p,Path(a['source']),Path(a['source_snapshot']),Path(a['raw_log']),Path(a['original_actual_runner']['file'])])
assert records[2]['actual_emitted_warning_diagnostics']==[] and records[2]['entire_raw_log']==''
dependencies=[ROOT/'verification/lean/SafeLearning/CompleteFoundationsSpectralModels.lean',ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean',ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean']
files+=dependencies
aliases={}
for p in dict.fromkeys(files):
    target=OUT/'original-closed-bytes'/sha(p)/p.name;target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb')as f:f.write(p.read_bytes())
    assert sha(target)==sha(p);aliases[str(p)]=ref(target)
clauses=[
    'The source function is exactly x1*x2/(x1^2+x2^2). Real division by zero gives its declared value0 at the origin. Both entire coordinate-axis restrictions are identically0, and their actual one-variable HasDerivAt derivatives at0 are0. No counterexample substitute is used.',
    'For every nonzero real t, the actual diagonal value f(t,t) is1/2; the point0 is explicitly excluded from this clause because the source declares f(0)=0.',
    'An actual epsilon-delta contradiction with output tolerance1/4 and input point(delta/4,delta/4) proves lack of continuity at0. Actual differentiability and C1 each imply continuity, so this same function has neither property at0 despite both actual zero coordinate partials.',
    'For arbitrary finite Euclidean coordinates I, C1ExtensionOn records exactly a chosen extension that agrees with the source restriction on S, an open set containing S, and actual ContDiffOn R1 regularity on that open set. This is the literal convention, not an assumption that its intended gradient exists. Open-neighborhood regularity derives actual HasGradientAt for that extension at every point of S.',
    'If S is closed, every frontier point lies in S; at each such point the chosen extension agrees with the restricted source and has an actual gradient. The ambient completion of an arbitrary function agreeing only on S need not be differentiable, and different extensions on a thin set need not have identical gradients. No extension uniqueness or arbitrary-completion regularity is claimed.'
]
j={'status':'prepared_tmp_actual7_body_one_full_literal_source_semantic_review_request','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/foundations_recovery28','current_inventory':ref(invp),'current_foundations_owner':ref(ownerp),'proof_source':ref(source),'entire_source':text,'public_theorem_count':7,'all_public_declarations':[ns+n for n in names],'full_source_units':[unit],'full_source_context_lines129_to218':'\n'.join(html.read_text().splitlines()[128:218]),'current_pending_claims_unchanged':[c for c in owner['material_claims']if key in c['source_unit_keys']],'complete_literal_clause_correspondences':[{'key':key,'lean_declarations':[ns+n for n in names],'complete_literal_correspondence':clauses}],'previous_packaging_failure_observation':{'file':'/tmp/foundations-literal-partial7-packaging-failure1-observation.json','sha256':sha(Path('/tmp/foundations-literal-partial7-packaging-failure1-observation.json'))},'entire_original_packaging_failure_observation':json.loads(Path('/tmp/foundations-literal-partial7-packaging-failure1-observation.json').read_text()),'actual_trials_original_bodies_and_times':records,'actual_successful_trial':records[2]['record'],'actual_successful_emitted_warning_diagnostics':0,'prior_trial2_real_pass_scope':'Trial2 genuinely passed the narrower R2 C1-extension convention. Trial3 genuinely passes the same counterexample plus the source convention for arbitrary finite Euclidean coordinate spaces; trial2 evidence remains unchanged.','all_reused_dependency_sources':[{'source':ref(p),'entire_source':p.read_text()}for p in dependencies],'original_closed_byte_aliases':aliases,'independent_whole_unit_approval':False,'canonical_installation_or_aggregate_verification_claimed':False,'review_request':'Read the seven complete theorem bodies and definitions, the entire exact literal186 with its full source context, and every complete reused dependency/primary source. Check the actual zero coordinate partials, diagonal exception at0, genuine discontinuity and differentiability/C1 contradiction, and the arbitrary finite-coordinate closed-set open-neighborhood extension convention including its precise boundary interpretation. Preserve real trial1 failure, narrower real trial2 pass, strengthened real trial3 pass and all original source/raw/body/times; compilation and integrity alone do not establish source correspondence. Decide whole literal186 explicitly or list missing clauses.','scope':'TMP-only full-unit request. Current55/1175/31/five are unchanged; no canonical source/proof/owner/mapping installation or whole-unit approval occurs.'}
p=OUT/'foundations-literal-partial7-full-review28-v2.json'
with p.open('xb')as f:f.write(encoded(j))
print(json.dumps({'packet':ref(p),'actual_successful_trial':j['actual_successful_trial'],'full_literal_units':1,'public_theorems':7,'closed_originals':len(aliases),'actual_warning_count':0}))
