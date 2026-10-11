from pathlib import Path
import json,hashlib,re,datetime
ROOT=Path('/home/oxrexkevin/SafetyBased')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def resolve(p):return Path(p) if Path(p).is_absolute() else ROOT/p
def chk(r):
 p=resolve(r['file']);assert H(p)==r['sha256'],str(p);return p
def ref(p):return {'file':str(p),'sha256':H(p)}
request=Path('/tmp/foundations-compact-lyapunov-printed-route24-single-literal-full-source-review-request-v1.json')
assert H(request)=='e65ffdeaab97bf3f3b9356509ce8b226521243987009a9923279216529ef76af'
r=json.loads(request.read_text());inv=json.loads(chk(r['current_inventory']).read_text())
page=chk(r['source_page']);lines=page.read_text().splitlines(keepends=True)
for c in r['complete_source_contexts']:
 actual=''.join(lines[c['lines_start']-1:c['lines_end']]);assert actual==c['exact_lines'] or actual==c['exact_lines']+'\n'
u=r['material_units'][0];row=u['entire_inventory_record'];assert row==next(x for x in inv['material_source_units'] if x['key']==u['source_unit_key'])
assert row['key']=='primer-basics.html::node-1158'
src=chk(r['new_actual_source']);body=src.read_text();assert body==r['entire_new_source_and_eight_bodies']
assert not re.search(r'\b(sorry|admit|axiom)\b',body)
names=['SafeLearning.CompleteFoundationsCompactLyapunovPrintedRoute24.'+n for n in re.findall(r'^theorem\s+(\w+)',body,re.M)]
assert len(names)==8 and names==r['public_theorem_names']
records=[]
for old in r['actual_trial_history']:
 rec=json.loads(chk(old['record']).read_text());assert rec==old['entire_original_actual_record'] and rec['actual_exit_code']==0
 snapshot=chk(old['source_snapshot']);log=chk(old['raw_log']);runner=chk(old['actual_runner'])
 assert H(snapshot)==rec['source_sha256_before']==rec['source_sha256_after']==rec['source_snapshot_sha256']
 assert H(log)==rec['raw_log_sha256'] and H(runner)==rec['actual_runner_sha256']
 assert rec['actual_command']==['lake','env','lean',rec['source']] and rec['actual_workdir']==str(ROOT/'verification/lean')
 assert 'error' not in log.read_text().lower() and len(re.findall(r': warning:',log.read_text()))==1
 records.append(old)
assert len(records)==2 and records[-1]['source_snapshot']['sha256']==H(src)
dep=r['selected_dependency'];dsrc=chk(dep['source']);assert dsrc.read_text()==dep['entire_body']
for p,h in dep['proof_file_row']['evidence_sha256'].items():assert H(ROOT/p)==h
for x in r['direct_primary_mathlib_sources']:chk(x)
manifest=json.loads(chk(r['protected_selected22_manifest']).read_text());assert len(manifest['proof_files'])==1113
for p,d in manifest['proof_files'].items():assert H(ROOT/p)==d['sha256'],p
for p,d in r['current_installed23_owner_and_source_guards'].items():assert H(ROOT/p)==d,p
chk(r['held_final_foundation23_offer'])
unit={'source_unit_key':row['key'],'entire_inventory_record':row,'unit_text_sha256':row['text_sha256'],'source_sha256':row['source_sha256'],'review_status':'independent_whole_source_review_passed','material_status':'proved','whole_unit_approved':True,'lean_declarations':u['lean_declarations'],'hypotheses':u['hypotheses'],'components':u['candidate_components'],'per_unit_reason':'All four printed steps were fully read against the new eight bodies and the selected induction/antitone dependency. Positive hypothetical infimum gives a nonempty closed annulus in the actual compact sublevel; the true continuous decrement attains a negative maximum there, deriving eta rather than assuming it. Actual recurrence yields the stated linear bound and atBot limit, contradicting nonnegative values. The second compact annulus yields a positive attained image minimum and eventual norm bounds, with its empty case handled explicitly. Global nonnegativity follows from the adjacent V0=0/positive-away-from0 assumptions.','missing_clauses':[]}
out=Path('/tmp/foundations-compact-lyapunov-printed-route24-single-literal-independent-applied-review-v1.json');assert not out.exists()
report={'status':'independent_whole_literal_source_review_passed','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/applied_next','request':ref(request),'current_inventory':r['current_inventory'],'source_page':r['source_page'],'material_units':[unit],'proof_sources':[r['new_actual_source'],dep['source']],'actual_trial_history':records,'complete_source_contexts':r['complete_source_contexts'],'selected_dependency':dep,'direct_primary_mathlib_sources':r['direct_primary_mathlib_sources'],'protected_selected22_manifest':r['protected_selected22_manifest'],'protected_selected22_source_count':1113,'current_installed23_owner_and_source_guards':r['current_installed23_owner_and_source_guards'],'held_final_foundation23_offer':r['held_final_foundation23_offer'],'checker':ref(Path(__file__)),'scope':'Fresh TMP-only full1158 review. Original actual seven-body trial1 and distinct eight-body trial2, both passed with one warning, remain unchanged; no new Lean run, named/canonical build, ledger/selection, full neighboring1163 audit or aggregate24 claim.'}
out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'review':str(out),'sha256':H(out),'whole_unit_approved':True,'full_new_theorem_count':8}))
