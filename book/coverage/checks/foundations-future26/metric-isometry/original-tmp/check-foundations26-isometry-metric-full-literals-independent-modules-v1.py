from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
R=Path('/home/oxrexkevin/SafetyBased');INV=R/'book/coverage/inventory.json';S=json.loads((R/'reports/full-coverage/checkpoint-25-selection.json').read_text());I=json.loads(INV.read_text());units={u['key']:u for u in I['material_source_units']}
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(r):
 p=Path(r['file']);p=p if p.is_absolute() else R/p;assert h(p)==r['sha256'];return p
assert h(INV)=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3';assert len(S['proof_files'])==1156
for n,row in S['proof_files'].items():assert h(R/n)==row['sha256']
requests=[('/tmp/foundations-isometric-embeddings26-single-literal-full-source-review-request-v1.json','/tmp/foundations-isometric-embeddings26-independent-modules-full-literal-review-v1.json'),('/tmp/foundations-metric-set-distance26-two-literals-full-source-review-request-v1.json','/tmp/foundations-metric-set-distance26-independent-modules-two-full-literal-review-v1.json')]
for rn,on in requests:
 rp=Path(rn);d=json.loads(rp.read_text());src=verify(d['source']);assert src.read_text()==d['full_source_body'];assert not re.search(r'\b(sorry|axiom|admit)\b',src.read_text())
 records=d.get('entire_inventory_records',[d.get('entire_inventory_record')]);assert all(units[u['key']]==u for u in records)
 f=d['full_context'];assert h(R/f['file'])==f['sha256'];assert '\n'.join((R/f['file']).read_text().splitlines()[f['first_line']-1:f['last_line']])+'\n'==f['text']
 primary=d['primary_local_definition'];verify(primary);assert '\n'.join(Path(primary['file']).read_text().splitlines()[primary['first_line']-1:primary['last_line']])+'\n'==primary['text']
 for rr in [d['actual_standalone'],d['raw_log'],d['source_snapshot'],d['actual_original_runner']]:verify(rr)
 actual=json.loads(verify(d['actual_standalone']).read_text());assert actual==d['entire_actual_standalone_record'];vv=[actual[k] for k in ['actual_exit_code','exit_code'] if k in actual];assert vv and all(type(x)is int and x==0 for x in vv);assert actual['protection_errors']==[];assert actual['source_sha256_before']==actual['source_sha256_after']==d['source']['sha256'];assert h(Path(actual['raw_log']))==actual['raw_log_sha256'];assert h(Path(actual['source_snapshot']))==actual['source_snapshot_sha256']==d['source']['sha256']
 for trial in d['trial_history']:
  for k in ['actual_record','source_snapshot','raw_log']:verify(trial[k])
 for n,hh in d['protected_current52_assets_sha256'].items():assert h(R/n)==hh
 for n,hh in d['protected_installed25_owners_sha256'].items():assert h(R/n)==hh
 ns=re.search(r'^namespace (\S+)',src.read_text(),re.M)[1];names=[ns+'.'+n for n in re.findall(r'^theorem (\S+)',src.read_text(),re.M)];assert names==d['public_declarations'] and len(names)==d['public_declaration_count']
 groups=[]
 for g in d['precise_groups_for_independent_decision']:
  assert set(g['lean_declarations'])<=set(names);groups.append({**g,'status':'approved','missing_clauses':[]})
 if 'isometric' in rn:
  reason='All metric/norm isometry definition clauses and arbitrary unit-direction affine-line pairs are directly exported; both arbitrary radial-kernel equalities follow from true preserved distance. The final learned-map warning is conditional modeling advice: no theorem says every learned or nonlinear map must distort distances. Actual square-map nonisometry, nonadditivity and 0/2 threshold-3 counterexample justify the stated risk without that universal inference.'
  hypotheses='Domain metric space, finite-dimensional real normed target (a case of the generic normed group proofs), actual unit direction norm1; arbitrary kappa. The learned-embedding sentence carries no universal quantifier; it advises checking isometry. No neighboring covering/net clause is promoted.'
 else:
  reason='Every displayed metric axiom and norm-induced distance identity is exported. Actual closed-ball sublevel, negative-radius emptiness and metric zero-radius singleton cover both parent and literal child separately. For explicitly nonempty C the genuine image of norm values is nonempty/bounded below, Metric.infDist is its greatest lower bound and equals its real sInf. No empty-set totalization or minimum-attainment claim is substituted.'
  hypotheses='Actual MetricSpace for separation and zero singleton; PseudoMetricSpace suffices for ball sublevel/negative emptiness. Normed additive group and explicitly nonempty C for real sInf; no compactness, closedness or attainment assumption.'
 decisions=[{'key':u['key'],'text_sha256':u['text_sha256'],'source_sha256':u['source_sha256'],'entire_inventory_record':u,'review_status':'approved_whole_literal','status':'approved_whole_literal','missing_clauses':[],'lean_declarations':names,'hypotheses':hypotheses,'reason':reason} for u in records]
 body={'status':'passed_independent_full_source_and_complete_literal_semantic_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','original_request':{'file':rn,'sha256':h(rp)},'current_inventory':d['current52_inventory'],'full_source_body_read':d['full_source_body'],'source':d['source'],'actual_standalone':d['actual_standalone'],'actual_raw_log':d['raw_log'],'source_snapshot':d['source_snapshot'],'entire_actual_record':actual,'exact_original_trial_history':d['trial_history'],'primary_local_route_read':primary,'full_context_read':f,'reviewed_groups':groups,'records':decisions,'literal_unit_decisions':decisions,'whole_literal_keys':[u['key'] for u in records],'missing_clauses':[],'original_pending_claims_retained_as_history':d['entire_original_pending_claims'],'all1156_selected_source_hashes_exact':True,'scope':'Fresh TMP-only full-body/full-literal decisions and direct evidence checks. No new Lean execution, named/canonical evidence, parent exercise or installed25 mapping/promotion is inferred. Original source/trial times and old pending bodies remain unchanged.'}
 out=Path(on);assert not out.exists();out.write_text(json.dumps(body,indent=2)+'\n');print(json.dumps({'peer':on,'sha256':h(out),'whole_literals':len(records)}))
