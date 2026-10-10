from pathlib import Path
import json, hashlib, datetime, re
root=Path('/home/oxrexkevin/SafetyBased')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
source='verification/lean/SafeLearning/CompleteModulesLandscapeRegularBoundaryPerturbation.lean'
assert sha(root/source)=='b447171cb28ea6e4b70a35805040974bb8087e0610493767a5b16ab2f9240094'
body=(root/source).read_text()
assert not re.search(r'\b(sorry|admit|axiom)\b',body)
names=re.findall(r'^theorem\s+(\w+)',body,re.M); assert len(names)==4
ev=[]
for rel in ['book/coverage/checks/modules-landscape-regular-boundary-perturbation19-trial2-standalone.json','book/coverage/checks/modules-landscape-regular-boundary-perturbation19-local-dependency-named-build.json']:
 d=json.loads((root/rel).read_text()); f=d['files'][0]
 assert f['file']==source and f['sha256']==sha(root/source) and f['exit_code']==0 and f['source_unchanged']
 assert sha(root/f['log'])==f['log_sha256']
 ev.append({'path':rel,'sha256':sha(root/rel),'actual_record':d,'raw_log_empty':(root/f['log']).stat().st_size==0})
failure='book/coverage/checks/modules-landscape-regular-boundary-perturbation19-trial1-standalone.json'
fd=json.loads((root/failure).read_text()); ff=fd['files'][0]
snapshot=Path('/tmp/modules-landscape-regular-boundary-perturbation19-trial1-source.lean')
assert ff['exit_code']!=0 and sha(snapshot)==ff['sha256'] and sha(root/ff['log'])==ff['log_sha256']
oldp=Path('/tmp/modules-future19-held-work-index-v13.json'); old=json.loads(oldp.read_text())
for p,h in old['held_pre33_metadata_sha256'].items():assert sha(root/p)==h
ip=root/'book/coverage/inventory-after-correction33.json'; inv=json.loads(ip.read_text());assert sha(ip)==old['current_inventory']['sha256']
for p,h in inv['source_sha256'].items():assert sha(root/p)==h
selp=root/'reports/full-coverage/checkpoint-18-selection.json';sel=json.loads(selp.read_text());assert sha(selp)==old['selected_checkpoint18_integrity']['selection_sha256']
protected={}
for p,v in sel['proof_files'].items():protected[p]=v['sha256'];protected.update(v['evidence_sha256'])
assert len(sel['proof_files'])==490 and len(protected)==565 and all(sha(root/p)==h for p,h in protected.items())
mp=root/'reports/full-coverage/checkpoint-18-manifest.json';m=json.loads(mp.read_text());assert sha(mp)==old['selected_checkpoint18_integrity']['frozen_manifest_sha256']
assert len(m['frozen_inputs_sha256'])==2431 and all(sha(root/m['snapshot']/p)==h for p,h in m['frozen_inputs_sha256'].items())
unit=next(u for u in inv['material_units'] if u['key']=='landscape.html::node-1338')
groups=[
 {'declaration':names[0],'status':'approved_complete_component','hypotheses':['Real normed vector space; the actual continuous linear differential is nonzero.'],'assessment':'Extensionality derives a vector with nonzero differential value; its sign chooses that vector or its negative, constructing an actual positive inward direction.','missing':[]},
 {'declaration':names[1],'status':'approved_complete_component','hypotheses':['Open D, C1 h on D, x0 in D and nonzero differential there.','The actual F Lie derivative is nonnegative at every h-zero in D; positive perturbation epsilon.'],'assessment':'C1 implies continuity of the evaluated differential. A genuine neighborhood keeps the chosen constant direction positive. The weak boundary derivative and epsilon times the positive differential then give a strictly positive boundary derivative for F+epsilon*v in that neighborhood. No Lipschitz derivative of h or desired invariance is assumed.','missing':[]},
 {'declaration':names[2],'status':'approved_complete_component','hypotheses':['Scalar path continuous on Icc a b, true right derivative on Ico a b, nonnegative initial value.','The derivative is strictly positive whenever the path equals zero.'],'assessment':'Applies the genuine right-derivative boundary fencing theorem to the negative path and the zero constant, deriving nonnegativity at every time including the endpoint. This is a strict condition; weak derivative at zeros alone is not claimed sufficient.','missing':[]},
 {'declaration':names[3],'status':'approved_complete_component','hypotheses':['Open D, C1 h, continuous actual path in D on Icc a b.','The path satisfies the true vector ODE right derivative on Ico a b.','Nonnegative initial h and strictly positive actual Lie derivative at all h-zero states in D.'],'assessment':'The actual chain rule derives the scalar path derivative, continuity follows by composition, and strict fencing gives h(path t)>=0 on the full existing interval. No conclusion is supplied as a premise.','missing':[]}
]
obj={'schema_version':1,'kind':'independent_regular_boundary_constant_perturbation_and_strict_fencing_component_review','reviewer':'/root/modules_resume','reviewed_at_utc':now,'status':'approved_four_precise_components_only','source':'SafeLearning/landscape.html','source_sha256':sha(root/'SafeLearning/landscape.html'),'inventory':str(ip.relative_to(root)),'inventory_sha256':sha(ip),'exact_material_unit':unit,'proof_source_sha256':{source:sha(root/source)},'actual_standalone_and_named_evidence':ev,'source_body_independently_fully_read':True,'theorem_groups':groups,'whole_material_unit_status':'pending_not_promoted','whole_exercise_status':'pending_not_promoted','remaining_gaps':['Weak regular-boundary-only Nagumo invariance still needs the genuine uniform perturbation solution limit and propagation; the four strict components alone do not prove it.','No full RKHS concentration, arbitrary QP solution regularity, statistical learned residual or fresh selected aggregate/kernel/axiom audit is inferred.'],'failed_history_preserved':{'manifest':failure,'sha256':sha(root/failure),'actual_record':fd,'source_snapshot':str(snapshot),'source_snapshot_sha256':sha(snapshot)},'preservation_check':{'selected_sources':490,'unique_source_evidence_paths':565,'frozen_inputs':2431,'current_inventory_pages':29,'all_hashes_exact':True,'held_pre33_metadata_exact':True,'prior_index':str(oldp),'prior_index_sha256':sha(oldp)},'limits':['TMP-only independent review during HOLD33; no source/inventory/ledger/coverage/selection mutation.','Actual trial2 standalone log is empty; named build success text is retained in its genuine nonempty raw log.','Passing source and historical failed snapshot/records/logs remain immutable.']}
out=Path('/tmp/modules-landscape-regular-boundary-perturbation-components-review19-v1.json');assert not out.exists();out.write_text(json.dumps(obj,indent=2)+'\n');print(json.dumps({'path':str(out),'sha256':sha(out),'components':len(groups),'protected_exact':True}))
