from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');REQ=Path('/tmp/foundations-literal-partial7-full-review28-v3/foundations-literal-partial7-full-review28-v3.json');OUT=Path('/tmp/foundations-literal-partial7-independent-applied-observations28-v1.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(REQ)=='8429c73be890d12639d782720ab9bb280a5bd9a4449aea37ab7ffa5d67184b2c'
d=json.loads(REQ.read_bytes());source=Path(d['proof_source']['file']);text=source.read_text();assert sha(source)==d['proof_source']['sha256']=='5caaf0d58af8a86977b4fbca8195d534c10464ba1dfc6703ae4d1fb750b99a3c' and text==d['entire_source']
assert len(re.findall(r'^theorem ',text,re.M))==d['public_theorem_count']==len(d['all_public_declarations'])==7
assert re.findall(r'^theorem\s+(\w+)',text,re.M)==[n.rsplit('.',1)[1] for n in d['all_public_declarations']]
inv=json.loads((ROOT/'book/coverage/inventory.json').read_bytes());owner=json.loads((ROOT/'book/coverage/foundations.json').read_bytes())
assert sha(ROOT/'book/coverage/inventory.json')==d['current_inventory']['sha256']=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
assert sha(ROOT/'book/coverage/foundations.json')==d['current_foundations_owner']['sha256']
unit=next(r for r in inv['material_source_units'] if r['key']=='primer-optimization.html::node-186');assert d['full_source_units']==[unit]
page=ROOT/unit['source'];assert sha(page)==unit['source_sha256']
assert '\n'.join(page.read_text().splitlines()[128:218])==d['full_source_context_lines129_to218']
old=[r for r in owner['material_claims'] if unit['key'] in r['source_unit_keys']];assert old==d['current_pending_claims_unchanged']
for row in d['all_reused_dependency_sources']:
 p=Path(row['source']['file']);assert sha(p)==row['source']['sha256'] and p.read_text()==row['entire_source']
for original,row in d['original_closed_byte_aliases'].items():
 p=Path(original);q=Path(row['file']);assert sha(p)==sha(q)==row['sha256']
trials=[]
for i,t in enumerate(d['actual_trials_original_bodies_and_times'],1):
 p=Path(t['record']['file']);native=json.loads(p.read_bytes());assert sha(p)==t['record']['sha256'] and native==t['entire_original_record_and_time']
 assert type(native['actual_exit_code']) is int and native['actual_exit_code']==(1 if i==1 else 0) and native['protection_errors']==[]
 raw=Path(native['raw_log']);snapshot=Path(native['source_snapshot']);original=Path(native['source'])
 assert sha(original)==sha(snapshot)==native['source_sha256_before']==native['source_sha256_after']==native['source_snapshot_sha256']
 assert snapshot.read_text()==t['entire_original_source'] and sha(raw)==native['raw_log_sha256'] and raw.read_text()==t['entire_raw_log']
 warnings=re.findall(r'^.+\.lean:\d+:\d+: warning:.*$',raw.read_text(),re.M);assert warnings==t['actual_emitted_warning_diagnostics']==[]
 trials.append({'record':t['record'],'actual_exit_code':native['actual_exit_code'],'finished_at_utc':native['finished_at_utc'],'warning_count':0})
assert d['actual_successful_trial']==d['actual_trials_original_bodies_and_times'][2]['record']
# Distinct v3 replaces only R2-specific extension definitions and the last two theorem signatures, retaining exact rational-example theorem bodies.
v2=Path('/tmp/CompleteFoundationsLiteralPartialPitfall28-draft-v2.lean').read_text()
assert text[:text.index('/-- The source convention')]==v2[:v2.index('/-- The source convention')]
for marker in ['def literalPitfall','HasDerivAt (fun t => literalPitfall (point t 0)) 0 0','(t : ℝ) (ht : t ≠ 0)','¬ ContinuousAt literalPitfall','¬ DifferentiableAt ℝ literalPitfall','¬ ContDiffAt ℝ 1 literalPitfall','structure C1ExtensionOn {I : Type*} [Fintype I]','regular : ContDiffOn ℝ 1 extension neighborhood','agrees : EqOn extension f S','HasGradientAt extension.extension (gradient extension.extension x) x','frontier_subset_closure']:
 assert marker in text,marker
result={'status':'passed_independent_literal186_full_source_bindings_and_semantic_review28','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':{'file':str(REQ),'sha256':sha(REQ)},'proof_source':d['proof_source'],'all_public_declarations':d['all_public_declarations'],'full_source_unit':unit,'full_context_read':True,'full_selected_spectral_source_read':True,'primary_C1_and_gradient_semantics':'ContDiffOn on an open neighborhood supplies ContDiffAt at every S point, which gives genuine DifferentiableAt and HasGradientAt for the chosen extension in every finite Euclidean dimension. A closed S contains its frontier. EqOn supplies exactly the source restriction values. No regularity of arbitrary other ambient completions or uniqueness across thin-set extensions is inferred.','whole_source_unit_approved':True,'missing_clauses':[],'scope_qualifications':['The diagonal value1/2 is for t!=0, as required by the declared value f(0)=0. Both actual coordinate restrictions are identically zero; these are genuine derivative witnesses.','The explicit delta/4 diagonal point contradicts actual continuity at0; differentiability and C1 imply continuity and hence fail at0.','The closed-set C1 clause is the printed chosen open-neighborhood extension convention. The gradient is that chosen C1 extension at every S/frontier point; a different arbitrary ambient completion or uniqueness on a thin S is not asserted.','The boundary theorem requires S closed; the extension-gradient theorem works at all S points without needing closedness. Arbitrary finite coordinate sets I, including zero dimension, are covered.'],'current_pending_claims_unchanged':old,'genuine_native_trials':trials,'original_packaging_failure_refs':[d['previous_packaging_failure_observation']], 'original_alias_count':len(d['original_closed_byte_aliases']),'canonical_or_whole_ledger_write_claimed':False,'compiler_rerun':False}
with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'observations':str(OUT),'sha256':sha(OUT),'whole_source_unit_approved':True,'missing_clauses':[],'aliases':len(d['original_closed_byte_aliases'])}))
