from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
R=Path('/home/oxrexkevin/SafetyBased');H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest();J=lambda n:json.loads((R/n).read_text());ref=lambda n:{'file':str(n),'sha256':H(n)}
request='/tmp/foundations-quadratic-twenty-net25-basics1175-full-source-review-request-v1.json';assert H(request)=='6542640d11bf69e95b9c3bbec501e3a5c9438b1760f2c91e6941d6c8285f8ea4';x=J(request)
source=x['proof_source'];assert H(source['file'])==source['sha256']=='3f2caf3abc7f228d63581ce31aba7144c213d830dfe5f0f009878ab2329f2a24';text=(R/source['file']).read_text();assert text==x['entire_source_and_all17_public_bodies']
names=['SafeLearning.CompleteFoundationsQuadraticTwentyNet24.'+v for v in re.findall(r'^theorem\s+([A-Za-z_][A-Za-z0-9_]*)',text,re.M)];assert names==x['public_theorem_names'] and len(names)==17;assert not re.search(r'\bsorry\b|\badmit\b|^axiom ',text,re.M)
for n,h in x['original_all_failed_and_passed_trial_artifact_sha256'].items():assert H(n)==h,n
raw=x['actual_TMP_standalone'];ar=J(raw['reference']['file']);assert H(raw['reference']['file'])==raw['reference']['sha256'] and ar==raw['entire_original_record_body_and_time'];assert ar['actual_exit_code']==0 and ar['source_sha256_before']==ar['source_sha256_after']==source['sha256'];assert H(ar['source_snapshot'])==ar['source_snapshot_sha256']==source['sha256'];assert H(ar['raw_log'])==ar['raw_log_sha256'];assert (R/ar['raw_log']).read_bytes()==b''
exits=[J('/tmp/foundations-quadratic-twenty-net24-trial'+str(i)+'.json')['actual_exit_code'] for i in range(1,6)];assert exits==[1,1,1,1,0]
d=x['selected_CubicGrids_dependency'];assert H(d['reference']['file'])==d['reference']['sha256'] and (R/d['reference']['file']).read_text()==d['entire_source'];dr=J(d['actual_named_dependency_build']['file']);assert H(d['actual_named_dependency_build']['file'])==d['actual_named_dependency_build']['sha256'];assert dr['actual_exit_code']==0;assert H(dr['raw_log'])==dr['raw_log_sha256']
selection=J('reports/full-coverage/checkpoint-23-selection.json');depname=str(Path(d['reference']['file']).relative_to(R));assert selection['proof_files'][depname]==d['original_selected23_row']
for n,row in selection['proof_files'].items():assert H(n)==row['sha256']
assert len(selection['proof_files'])==1131
for n,h in d['original_selected23_row']['evidence_sha256'].items():assert H(n)==h
inv='book/coverage/inventory-after-correction52.json';assert H(inv)==H('book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3';v=J(inv);unit=next(a for a in v['material_source_units'] if a['key']=='primer-basics.html::node-1175');assert unit==x['entire_inventory_record']
context=x['complete_parent_section_context'];assert H(context['file'])==context['sha256'];lines=(R/context['file']).read_text().splitlines(keepends=True);assert ''.join(lines[context['lines_start']-1:context['lines_end']])==context['exact_lines']
assert H(x['held_foundation24_original_offer']['file'])==x['held_foundation24_original_offer']['sha256']
reasons=[
 'The actual derivative is −2x. Its absolute value has an attained greatest value19/10 on the printed interval, and the factorization h(x)−h(y)=(y−x)(x+y) derives the corresponding true Lipschitz bound.',
 'Both point maps are genuinely inside the printed interval, injective, and have exactly20/10 images and spacing1/10 or1/5. Exhaustive interval splits cover every actual x; explicit midpoints prove the radii1/20 and1/10 are least possible for those actual grids.',
 'The actual function has minimum39/400 at both endpoints. Fine samples attain it,19/200<39/400, and actual net plus Lipschitz inequalities give h≥1/400. The coarse first sample has39/400<19/100, so its sufficient margin test fails although h is strictly positive throughout the interval.',
 'Reducing radius raises the certified lower bound when the same valid sample floor and Lipschitz constant are used; this applies directly to the actual positive-floor example. For the actual fixed-dimensional cube grid, count=(N+1)^d lies betweenN^d and2^dN^d, with radius=sqrt(d)/(2N), substantiating the stated mesh cost. Section7 line1368 directly states m points per axis produce m^d points; only this local grid-cost attribution is checked.'
]
groups=[]
for g,reason in zip(x['expected_precise_groups'],reasons):
 assert all(n in names for n in g['decls']);groups.append({'id':g['id'],'review_status':'approved_complete_source_component','decls':g['decls'],'hypotheses':x['hypotheses'],'reason':reason,'missing':[]})
assert set(n for g in groups for n in g['decls'])==set(names)
now=datetime.now(timezone.utc).isoformat();result={'status':'independent_full_literal_semantic_source_review_passed','errors':[],'reviewer':'/root/modules_resume','reviewed_at_utc':now,
 'request':ref(request),'inventory':ref(inv),'source':source,'entire_source_and_all17_public_bodies_read':True,'entire_source_body':text,'public_theorem_names':names,
 'groups':groups,'material_units':[{'inventory_key':unit['key'],'inventory_record':unit,'key':unit['key'],'text_sha256':unit['text_sha256'],'source_sha256':unit['source_sha256'],
 'review_status':'approved_complete_source_clause','status':'approved_complete_source_clause','whole_material_unit_approved':True,'decls':names,'hypotheses':x['hypotheses'],
 'reason':'Every clause of the complete literal1175 is matched by the actual grids, scalar function, all-point sample-margin route and selected cube cost. Finer-grid advice is interpreted in the stated positive-floor example and explicit same-valid-floor comparison; it does not assert arbitrary sample minima remain equal.','missing':[],'reviewed_at_utc':now}],
 'whole_material_units_approved':[unit['key']],'whole_exercises_approved':[],
 'actual_TMP_standalone_record_reference':raw['reference'],'entire_original_actual_standalone_body_and_time':ar,
 'actual_dependency_named_build':d['actual_named_dependency_build'],'selected_dependency':d['reference'],'retained_selected23_row':d['original_selected23_row'],
 'all_original_trial_artifact_sha256':x['original_all_failed_and_passed_trial_artifact_sha256'],'genuine_trial_exit_codes':exits,
 'direct_local_section7_grid_cost_passage':{'file':context['file'],'sha256':context['sha256'],'line':1368,'exact_line':lines[1367]},
 'all1131_selected_source_hashes_exact':True,
 'scope_limits':['One complete actual grid example only; no surrounding covering-number theorem, parent exercise or entire Section7 approved.',
 'Finer-radius comparison retains its same-valid-sample-lower-bound premise. No universal claim that replacing arbitrary sampling grids preserves their minimum sample value.',
 'Mesh cost is for this actual cube grid at fixed positive dimension as N increases; no universal covering-number lower bound or runtime statement.',
 'Source filename has24 but this reviewed pack is explicitly unselected future25. New source has genuine TMP standalone only, no new canonical/named/live/aggregate claim.']}
out=Path('/tmp/foundations-quadratic-twenty-net25-basics1175-independent-modules-full-source-review-v1.json');assert not out.exists();out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'report':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}))
