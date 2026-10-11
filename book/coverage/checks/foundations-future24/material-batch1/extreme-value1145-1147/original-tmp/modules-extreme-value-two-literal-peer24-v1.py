from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.dont_write_bytecode=True
sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
Q=Path('/tmp/foundations-extreme-value-countermodels24-two-literals-full-source-review-request-v1.json')
O=Path('/tmp/foundations-extreme-value-two-literals-independent-modules-source-review24-v1.json')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(r):assert h(r['file'])==r['sha256'];return Path(r['file'])
assert not O.exists() and h(Q)=='15e209cd0e666da5286b7d05eb70cde9ce7cb9ace0c9c0386836cab651347c89'
q=json.loads(Q.read_text());source=check(q['new_actual_source']);assert source.read_text()==q['entire_source_and_all_eleven_theorem_bodies']
names=[d['name'] for d in declarations(source.read_text()) if d['kind'] in ('theorem','lemma')]
assert len(names)==11 and names==q['new_public_theorem_names']
assert 'sorry' not in source.read_text() and 'axiom ' not in source.read_text()
actual=json.loads(check(q['actual_standalone_record']).read_text());assert actual['actual_exit_code']==0
assert actual['actual_command']==['lake','env','lean',str(source)] and actual['actual_workdir']==str(R/'verification/lean')
assert actual['source_sha256_before']==actual['source_sha256_after']==h(source)
assert h(check(q['actual_standalone_raw_log']))==actual['raw_log_sha256'] and check(q['actual_standalone_raw_log']).read_bytes()==b''
for row in q['entire_actual_trial_history']:
    a=json.loads(check(row['reference']).read_text());assert a==row['entire_actual_record']
    assert h(check(row['source_snapshot']))==a['source_sha256_before']==a['source_sha256_after']
    assert h(check(row['raw_log']))==a['raw_log_sha256']
dependency=q['direct_selected_dependency'];assert check(dependency['source']).read_text()==dependency['entire_source_body']
for r in q['direct_primary_mathlib_contexts']:
    p=check(r['source']);lines=p.read_text().splitlines(keepends=True)
    assert ''.join(lines[r['lines_start']-1:r['lines_end']])==r['exact_lines']
page=check(q['source_page']);context=q['complete_source_context'];lines=page.read_text().splitlines(keepends=True)
assert ''.join(lines[context['lines_start']-1:context['lines_end']])==context['exact_lines']
current=json.loads(check(q['current_inventory']).read_text());old=json.loads(check(q['original_unchanged48_inventory']).read_text())
bykey={r['key']:r for r in current['material_source_units']};oldkey={r['key']:r for r in old['material_source_units']}
for r in q['material_units']:
    assert r==bykey[r['key']]==oldkey[r['key']]
    assert h(page)==r['source_sha256'] and hashlib.sha256(r['source_text'].encode()).hexdigest()==r['text_sha256']
# Root has legitimately installed23; verify the original22 request ledger in its
# actual archive rather than relabeling the old mutable-path guard as current.
historical=q['original_held22_foundation_ledger'];archive=R/'reports/full-coverage/owner22-originals-before-owner23-integration-v1/foundations.json'
assert h(archive)==historical['sha256']=='305229a7e1df78c23bc1af728c7f3f4e0ac09d13c55e4e687fe721160b43bf88'
baseline=json.loads(check(q['protected_selected22_manifest']).read_text())
for n,p in baseline['proof_files'].items():assert h(R/n)==p['sha256']
groups=[
 {'id':'real_extrema_and_actual_extended_supremum','lean_declarations':[names[0],names[9]],'hypotheses':['Nonempty compact K and genuine continuous real-valued f on K.'],'reason':'Actual IsLeast/IsGreatest extrema are derived from compactness and continuity. The EReal supremum is exactly a finite attained real evaluation, so extended infinities are excluded by the conclusion.'},
 {'id':'printed_sequence_subsequence_route','lean_declarations':[names[10]],'hypotheses':['First-countable topology, supplied sequence entirely in compact K, continuous f on K and its actual EReal value limit M; Euclidean domains satisfy first-countability.'],'reason':'The printed initial choice of an approaching sequence is the intermediate premise, rather than the desired finite/attained conclusion. A strict subsequence and point in K are derived; continuous evaluation and uniqueness of the extended-real limit force f(a)=M and rule out both infinities. The separate finite-attainment theorem supplies a constant maximizing sequence if an explicit witness is needed.'},
 {'id':'nonclosed_and_unbounded_minimum_countermodels','lean_declarations':names[1:5],'hypotheses':['Exact real identity on (0,1] and exact exp(-x) on [0,infinity).'],'reason':'Both have actual greatest lower bound0 and no minimizing point. The first domain is proved nonclosed/noncompact; the second is proved closed but unbounded/noncompact. The word neither refers back to nonattainment of the infimum; no false absence of the exponential maximum at0 is inferred.'},
 {'id':'discontinuous_endpoint_maximum_countermodel','lean_declarations':names[5:9],'hypotheses':['Actual compact [0,1] and actual jump x for x<1, with jump(1)=0.'],'reason':'The actual image is [0,1), so supremum1 is not attained. A concrete sequence1-1/(n+1) proves discontinuity at1, and continuous-on failure on the compact domain is proved separately.'},
]
records=[]
for r in q['material_units']:
    records.append({'key':r['key'],'entire_original_inventory_record':r,'status':'proved','whole_unit_approved':True,'lean_declarations':names,'hypotheses':[h for g in groups for h in g['hypotheses']],'reason':'Individually read the complete generic extreme-value theorem, extended-supremum/subsequence proof and all three exact countermodels. All conclusions match the genuine proof declarations in the four groups, with explicit nonempty/compact/continuous domains and the initial approaching-sequence premise scoped.','missing_clauses':[]})
out={'status':'independent_complete_two_extreme_value_literal_source_review_passed_future24_TMP_only','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':{'file':str(Q),'sha256':h(Q)},'actual_source':q['new_actual_source'],'source_entire_body':source.read_text(),'actual_standalone_evidence':q['actual_standalone_record'],'actual_standalone_raw_log':q['actual_standalone_raw_log'],'actual_trial_history':q['entire_actual_trial_history'],'direct_selected_dependency':dependency['source'],'component_groups':groups,'material_units':records,'whole_unit_count':2,'missing_clauses':[],'errors':[],'historical_original22_owner_path_guard':historical,'actual_original22_archive_checked':{'file':str(archive.relative_to(R)),'sha256':h(archive)},'current_owner_live_assets_mutated':False,'scope':'Fresh full semantic read of two unchanged current51 literals using all eleven complete TMP theorem bodies and exact actual standalone0/empty log. No canonical/named execution, source/owner mapping, parent exercise closure or aggregate24 pass is inferred. Original trial failures and successful nine-body trial remain immutable.'}
O.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'report':str(O),'sha256':h(O)}))
