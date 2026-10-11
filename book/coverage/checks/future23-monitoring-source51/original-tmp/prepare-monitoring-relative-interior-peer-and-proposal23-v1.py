from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys,shutil,importlib.util
ROOT=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda p:{'file':str(p),'sha256':H(p)}
invfile=ROOT/'book/coverage/inventory-after-correction50.json';assert H(invfile)=='dec8a34d0313fbc19846489f4d8c2f6e51734a135df6145829993fae0f80d91c'
inv=json.loads(invfile.read_text());units={r['key']:r for r in inv['material_source_units']};u=units['cmdp.html::node-1138']
assert u['source_sha256']=='5a503475452eacbeb8d5b8f4b3dd846bc3d88ff6817bd900a3cf3b2e2b23f6e9'
proof=Path('/tmp/root-monitoring-exposed-interior23-trial1.lean');record=proof.with_suffix('.json');log=proof.with_suffix('.log');rr=json.loads(record.read_text())
assert H(proof)=='b6c91e28a41d20750254cff2451d82a6ac345d561cea96586629d22978b9b296'==rr['source_sha256'] and rr['exit_code']==0
assert H(log)==rr['log_sha256'] and log.read_bytes()==b''
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
names=[r['name'] for r in declarations(proof.read_text()) if r['kind'] in ['theorem','lemma']];assert len(names)==6
reasons=[
'The actual source Lagrangian, including its price-dependent constant, is affine under arbitrary real coordinate mixtures, by direct expansion and ring normalization.',
'Actual coordinate mixtures with t in[0,1] preserve every nonnegative/simplex/V0<=1/2 clause of the source achievable polytope; no desired closure premise.',
'The explicit exposed predicate means a unique actual Lagrangian maximizer; strict positive mixture weights force both endpoints to attain that maximum and uniqueness forces equality. This is the ordinary real coordinate extremality definition.',
'Actual nonnegative exposing prices(2,0),(0,2),(1/2,0),(0,1/2) invoke the genuine strict-branch iffs to derive unique exposure of each printed vertex.',
'Each of the four printed vertices satisfies actual polytope membership and the ordinary nontrivial-convex-mixture extremality property, derived from the true exposing witnesses.',
'Any fraction vector in the sum=1 plane whose three coordinate distances from1/3 are strictly less than1/12 is in the polytope. The open coordinate box intersected with this plane supplies a relative neighborhood of the optimum; it does not claim ambient R3 interior.'
]
deps=[ROOT/'verification/lean/SafeLearning/CompleteMonitoringGeometry21.lean',ROOT/'verification/lean/SafeLearning/CompleteMonitoringFaceClassification23.lean']
manifest=ROOT/'reports/full-coverage/checkpoint-22-manifest.json';m=json.loads(manifest.read_text())
for p,r in m['proof_files'].items():assert H(ROOT/p)==r['sha256']
peer={'status':'passed_independent_full_six_body_exposed_and_relative_interior_components_future23','reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'errors':[],'inventory':ref(invfile),'material_units':[{'source_unit_key':u['key'],'entire_inventory_record':u,'whole_unit_approved':False,'material_status':'pending','review_status':'approved_precise_geometry_components_only','lean_declarations':names,'hypotheses':['The literal Fractions object has three real coordinates. AchievablePolytope is coordinate nonnegativity, sum1, and V0<=1/2.','The interior clause is relative to the affine plane sum=1; the literal ambient-interior ambiguity is retained pending the separate phrase clarification.'],'per_unit_reason':'Full six bodies and definitions read: actual affine L, genuine coordinate convexity, exposed implies extreme, all four printed vertices exposed/extreme and an actual relative-plane neighborhood. Existing four-weight convex-hull identity and complete maximizing-case classification supply the quadrilateral and face interpretation.','missing_clauses':['This component peer alone is not the complete actual-policy realization/path review of(b).','Current source says interior without specifying the relative plane. No ambient R3 interior is asserted or approved.']}],'proof_source':ref(proof),'actual_standalone_record':ref(record),'entire_original_actual_standalone_record':rr,'raw_log':ref(log),'raw_log_is_actually_empty':True,'actual_original_runner':ref(proof.with_name(proof.stem+'-run.py')),'public_theorem_count':6,'all_six_full_bodies_and_definitions_read':True,'per_body_decisions':[{'lean_declaration':n,'review_status':'approved_complete_component','hypotheses':[],'reason':r,'missing_clauses':[]} for n,r in zip(names,reasons)],'full_dependencies_read':[ref(p) for p in deps],'whole_exercise_approved':False,'current_working_inputs_changed':False,'protected_selected22':{'manifest':ref(manifest),'proof_count':len(m['proof_files']),'all_exact':True},'actual_checker':ref(Path(__file__)),'limits':['No new Lean execution is claimed by this independent read/check.','No general A3 or epoch-execution theorem, complete(c), new coverage selection or aggregate23 audit.','The custom typed coordinate definitions express the standard convex/exposed/extreme properties for this exact real fraction polytope. No theorem asserting that these are its only extreme points is separately exported.']}
peerfile=Path('/tmp/monitoring-exposed-relative-interior23-independent-applied-components-review-v1.json');assert not peerfile.exists();peerfile.write_text(json.dumps(peer,indent=2,ensure_ascii=False)+'\n')
source=ROOT/u['source'];original=source.read_text();assert H(source)==u['source_sha256'];before='is an interior point';after=r'lies in the relative interior of the quadrilateral in the plane $V_0+V_1+V_2=1$'
assert original.count(before)==1;updated=original.replace(before,after,1);assert updated.replace(after,before,1)==original
assert '\n' not in before+after and updated.count('\n')==original.count('\n')
sys.path.insert(0,str(ROOT/'book'));from validate import Document
old,new=Document(original),Document(updated);assert len(old.nodes)==len(new.nodes) and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(old.nodes,new.nodes))
sim=Path('/tmp/applied-monitoring-relative-interior-source51-simulation23-v1');assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for p,sha in inv['source_sha256'].items():
 path=ROOT/p;assert H(path)==sha;dest=sim/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(path.read_bytes())
(sim/u['source']).write_text(updated)
spec=importlib.util.spec_from_file_location('monitoring_relative_interior_inventory51',ROOT/'book/inventory_claims.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);g.ROOT=sim;g.OUT=sim/'book/coverage';g.inventory();proposed=json.loads((g.OUT/'inventory.json').read_text());assert inv['counts']==proposed['counts']
changed={}
for sec in ['exercises','material_source_units']:
 a={r['key']:r for r in inv[sec]};b={r['key']:r for r in proposed[sec]};assert a.keys()==b.keys();changed[sec]=[]
 for key,row in a.items():
  other=b[key];assert row.keys()==other.keys()
  assert all(row[k]==other[k] for k in row if k not in ['source_text','text_sha256','source_sha256']),(key,'structural drift')
  if row['source_text']!=other['source_text']:changed[sec].append(key)
  else:assert row['text_sha256']==other['text_sha256']
  if row['source']!=u['source']:assert row==other
assert changed=={'exercises':['cmdp.html::exercise-21'],'material_source_units':['cmdp.html::node-1138']},changed
for p,r in m['proof_files'].items():assert H(ROOT/p)==r['sha256']
assert H(source)==u['source_sha256'] and H(ROOT/'book/coverage/inventory.json')==H(invfile)
proposal={'status':'read_only_future23_relative_interior_phrase_proposal_pending_independent_semantic_review','prepared_by':'/root/applied_next','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'source':u['source'],'source_sha256_before':H(source),'proposed_source_sha256_after':hashlib.sha256(updated.encode()).hexdigest(),'current_authoritative_inventory':ref(invfile),'entire_original_material_record':u,'entire_original_exercise':next(r for r in inv['exercises'] if r['key']=='cmdp.html::exercise-21'),'replacements':[{'source_unit_key':u['key'],'before':before,'after':after,'count':1,'reason':'The achievable quadrilateral lies in the affine sum=1 plane and has empty ambient R3 interior. The genuine radius1/12 plane-neighborhood theorem makes the intended relative interior statement precise.'}],'expected_changed_text_keys':changed,'proposed_material_record':next(r for r in proposed['material_source_units'] if r['key']==u['key']),'full29_page_parser':{'actual_parser_completed':True,'proposed_inventory':ref(g.OUT/'inventory.json'),'counts_unchanged':True,'all_keys_locators_lines_attributes_and_structural_fields_exact':True,'unique_forward_and_reverse_bytes_exact':True,'dom_node_signature_exact':True,'newlines_unchanged':True,'all_other_28_source_pages_exact':True,'root_source50_lyapunov_corrections_preserved':True},'precise_proof_source':ref(proof),'genuine_actual_standalone_record':ref(record),'new_independent_six_body_review':ref(peerfile),'protected_selected22':{'manifest':ref(manifest),'proof_count':len(m['proof_files']),'all_exact':True},'actual_preparer':ref(Path(__file__)),'working_HTML_inventory_ledgers_written':False,'correction_number_assigned':False,'whole_current_or_proposed_unit_approved':False,'whole_exercise_approved':False,'limits':['One phrase qualification only; all numerical/model/policy/selector/A3 wording retained byte-exact.','Proposal approval is independent from fresh complete(b) correspondence after the new canonical pair.','No source51 working write, coverage promotion, new Lean execution or aggregate23 claim.']}
out=Path('/tmp/applied-monitoring-relative-interior-source51-precision-proposal23-v1.json');assert not out.exists();out.write_text(json.dumps(proposal,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'peer':ref(peerfile),'proposal':ref(out),'changed':changed}))
