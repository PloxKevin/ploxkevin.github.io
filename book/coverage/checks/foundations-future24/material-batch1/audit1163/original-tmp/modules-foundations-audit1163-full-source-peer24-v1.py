from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys,copy
R=Path('/home/oxrexkevin/SafetyBased');sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
Q=Path('/tmp/foundations-compact-lyapunov-audit1163-single-literal-full-source-review-request24-v1.json')
O=Path('/tmp/foundations-audit1163-independent-modules-full-source-review24-v1.json')
assert not O.exists()
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def checked(r):
 p=Path(r['file']);assert p.is_absolute() and (p.is_relative_to(R) or p.is_relative_to(Path('/tmp')))
 assert H(p)==r['sha256'],str(p);return p
q=json.loads(Q.read_text());assert H(Q)=='bf44d889364a01b0a97395cd93c155cbd0f637af34dadd99ab64bdcd268925eb'
inv=json.loads(checked(q['current_inventory']).read_text());assert q['current_inventory']['sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
assert H(R/'book/coverage/inventory.json')==q['current_inventory']['sha256']
checked(q['source_page']);manifest=json.loads(checked(q['protected_selected22_manifest']).read_text())
for name,row in manifest['proof_files'].items():assert H(R/name)==row['sha256']
for name,d in q['current_installed23_owner_and_source_guards'].items():assert H(R/name)==d
source=checked(q['new_actual_source']);assert source.read_text()==q['entire_new_source_and_five_bodies']
exports=[d['name'] for d in declarations(source.read_text()) if d['kind'] in ('theorem','lemma')]
assert exports==q['public_theorem_names'] and len(exports)==5
assert 'sorry' not in source.read_text() and 'axiom ' not in source.read_text()
selected_names=set()
for dep in q['selected_dependencies']:
 p=checked(dep['source']);text=p.read_text();assert text==dep['entire_selected_source_and_all_bodies']
 n=p.relative_to(R).as_posix();assert dep['original_manifest_proof_file_row']==manifest['proof_files'][n]
 ds=[d['name'] for d in declarations(text) if d['kind'] in ('theorem','lemma')]
 assert set(ds)=={d['name'] for d in dep['original_actual22_public_declarations']}
 selected_names.update(ds)
audit=json.loads(checked(q['actual_selected22_aggregate']).read_text());assert audit['status']=='passed' and audit['proof_file_count']==1113 and audit['theorem_count']==9002
assert all(type(c['exit_code']) is int and c['exit_code']==0 for c in audit['checks'])
assert q['original_aggregate_checks_and_time']=={k:audit[k] for k in q['original_aggregate_checks_and_time']}
for dep in q['selected_dependencies']:
 n=Path(dep['source']['file']).relative_to(R).as_posix();assert audit['proof_sha256'][n]==dep['source']['sha256']
 checked_names={d['name'] for d in audit['declarations'] if d['file']==n};assert checked_names=={d['name'] for d in dep['original_actual22_public_declarations']}
old_request=json.loads(checked(q['original_printed_route_request']).read_text());assert old_request==q['entire_original_printed_route_request_body_and_time']
old_peer=json.loads(checked(q['original_printed_route_full_semantic_peer']).read_text());assert old_peer==q['entire_original_printed_route_full_peer_body_and_time'] and 'passed' in old_peer['status']
route=checked(old_request['new_actual_source']);assert route.read_text()==old_request['entire_new_source_and_eight_bodies']
route_names={d['name'] for d in declarations(route.read_text()) if d['kind'] in ('theorem','lemma')};assert len(route_names)==8
history=[]
for row in q['actual_trial_history']:
 actual=json.loads(checked(row['record']).read_text());assert actual==row['entire_original_actual_record']
 snap=checked(row['source_snapshot']);log=checked(row['raw_log']);checked(row['actual_runner'])
 assert actual['source_sha256_before']==actual['source_sha256_after']==H(snap)
 assert actual['raw_log_sha256']==H(log) and actual['actual_runner_sha256']==row['actual_runner']['sha256']
 assert type(actual['actual_exit_code']) is int
 assert actual['actual_command']==['lake','env','lean',actual['source']]
 assert actual['actual_workdir']==str(R/'verification/lean')
 history.append({'record':row['record'],'source_snapshot':row['source_snapshot'],'raw_log':row['raw_log'],'actual_exit_code':actual['actual_exit_code']})
assert [r['actual_exit_code'] for r in history]==[1,1,0]
assert history[-1]['source_snapshot']['sha256']==q['new_actual_source']['sha256'] and checked(history[-1]['raw_log']).stat().st_size==0
for ctx in q['complete_source_contexts']:
 p=checked(ctx['source']);lines=p.read_text().splitlines();actual='\n'.join(lines[ctx['lines_start']-1:ctx['lines_end']])
 assert actual+'\n'==ctx['exact_lines'] or actual==ctx['exact_lines']
units={u['key']:u for u in inv['material_source_units']}
unit=q['material_units'][0];original=unit['entire_inventory_record'];assert units[original['key']]==original and original['key']=='primer-basics.html::node-1163'
allnames=selected_names|set(exports)|route_names
assert set(unit['lean_declarations'])<=allnames
reason=('The entire printed audit matches the genuine routes: the eight-body compact-annulus proof uses actual induction/antitone infimum convergence, an attained negative maximum, a positive attained away-from-zero minimum and contradiction. The actual discontinuous Module11 map has orbit1+2^-n tending to1, fixes0 and decreases squared values, but its negative increments have unattained supremum0 on the compact annulus. The new five bodies identify the printed nonlinear decrement as minus eta(Vx), prove eta(a)>0/monotonicity, use the actual sqrt(a) witness for the exact annulus maximum and derive eta(a)→0. The selected initial-one orbit has the actual ratio to1/sqrt(2n) tending to1. “The argument gives no rate” records the qualitative proof scope, not a claim that no rate for a particular system could ever be proved separately; the asymptotic fixture keeps its explicit Section2 initial state1.')
out={'status':'independent_full_literal_foundations_audit1163_source_review_passed','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','request':{'file':str(Q),'sha256':H(Q)},'current_inventory':q['current_inventory'],'source_page':q['source_page'],'material_units':[{'source_unit_key':original['key'],'entire_inventory_record':original,'review_status':'approved_complete_source_unit','lean_declarations':unit['lean_declarations'],'hypotheses':unit['hypotheses'],'reason':reason,'component_groups':copy.deepcopy(unit['candidate_components']),'missing':[]}],'proof_sources':[q['new_actual_source'],old_request['new_actual_source']]+[d['source'] for d in q['selected_dependencies']],'new_five_full_theorem_names':exports,'actual_trial_history':history,'original_printed_route_full_semantic_peer':q['original_printed_route_full_semantic_peer'],'original_printed_route_review_time_preserved':old_peer['reviewed_at_utc'],'original22_aggregate':q['actual_selected22_aggregate'],'protected_selected22_manifest':q['protected_selected22_manifest'],'protected_selected22_source_count':1113,'current_installed23_owner_and_source_guards':q['current_installed23_owner_and_source_guards'],'complete_source_contexts':q['complete_source_contexts'],'checker':{'file':str(Path(__file__)),'sha256':H(Path(__file__))},'errors':[],'scope':'Fresh TMP full literal review only. All original source/proof/review bodies and compiler/review times remain unchanged; no parent exercise, canonical/named24 build, live owner mapping, selection24, aggregate24 or publication pass is inferred. Internal Module11/Section2 attributions are checked only against the exact supplied local passages.'}
for name,d in q['current_installed23_owner_and_source_guards'].items():assert H(R/name)==d
assert H(Q)==out['request']['sha256'];O.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'report':str(O),'sha256':H(O)}))
