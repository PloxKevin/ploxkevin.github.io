"""Independent proposal-only semantic and fresh-parser review, with two source scopes."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,importlib.util,json,re,shutil,sys,traceback
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp')
REQUEST=TMP/'applied-lyapunov-scenario-validation-precision-proposal23-v1.json'
OUT=TMP/'lyapunov-precision-proposal23-independent-foundations-semantic-review-v1.json'
FAIL=TMP/'lyapunov-precision-proposal23-independent-foundations-checker-failure-v1.json'
START=datetime.now(timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p

def simulate(q,baseline_inventory,baseline_tree,label):
 source=q['source'];original=(baseline_tree/source).read_bytes();assert hashlib.sha256(original).hexdigest()==q['source_sha256_before']
 after=original
 for row in q['replacements']:
  a,b=row['before'].encode(),row['after'].encode()
  assert after.count(a)==1 and b'\n' not in a and b'\n' not in b and row['count']==1
  after=after.replace(a,b,1)
 reverse=after
 for row in reversed(q['replacements']):
  a,b=row['before'].encode(),row['after'].encode();assert reverse.count(b)==1;reverse=reverse.replace(b,a,1)
 assert reverse==original and after.count(b'\n')==original.count(b'\n')
 assert hashlib.sha256(after).hexdigest()==q['proposed_source_sha256_after']
 from validate import Document
 old_doc,new_doc=Document(original.decode()),Document(after.decode())
 assert len(old_doc.nodes)==len(new_doc.nodes)
 assert [(n.tag,n.attrs,n.line) for n in old_doc.nodes]==[(n.tag,n.attrs,n.line) for n in new_doc.nodes]
 sim=TMP/f'foundations-independent-lyapunov-precision23-{label}-simulation-v1'
 assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
 for p in (baseline_tree/'SafeLearning').glob('*.html'):
  shutil.copyfile(p,sim/'SafeLearning'/p.name)
 (sim/source).write_bytes(after)
 spec=importlib.util.spec_from_file_location('foundation_precision_inventory_'+label,ROOT/'book/inventory_claims.py')
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 module.ROOT=sim;module.OUT=sim/'book/coverage';module.inventory()
 parsed=read(module.OUT/'inventory.json');assert parsed['counts']==baseline_inventory['counts']
 assert len(parsed['source_sha256'])==len(baseline_inventory['source_sha256'])==29
 assert set(parsed['source_sha256'])==set(baseline_inventory['source_sha256'])
 assert {n for n in parsed['source_sha256'] if parsed['source_sha256'][n]!=baseline_inventory['source_sha256'][n]}=={source}
 changes={}
 for section in ('exercises','material_source_units'):
  old={r['key']:r for r in baseline_inventory[section]};new={r['key']:r for r in parsed[section]}
  assert old.keys()==new.keys();changed=[]
  for key,a in old.items():
   b=new[key];assert a.keys()==b.keys()
   assert all(a[f]==b[f] for f in a if f not in {'source_sha256','source_text','text_sha256'}),(label,key)
   if a['source_text']!=b['source_text']:changed.append(key)
   else:assert a['text_sha256']==b['text_sha256']
   if a['source']!=source:assert a==b
  changes[section]=changed
 assert changes==q['expected_changed_text_keys']
 return {'baseline':label,'actual_fresh_full29_page_parser_completed':True,'simulation_inventory':ref(module.OUT/'inventory.json'),'only_changed_literal_keys':changes,'all_keys_lines_attributes_locators_and_other_fields_exact':True,'DOM_signature_exact':True,'unique_forward_reverse_and_newline_bytes_exact':True}

def main():
 assert not OUT.exists() and not FAIL.exists()
 assert sha(REQUEST)=='8042bfa28aaa6056d2480ea96e242b37e4a5cea503b0960bd136048f51d208f9'
 q=read(REQUEST);old=read(check(q['original_inventory']))
 assert next(r for r in old['exercises'] if r['key']=='lyapunov-mpc.html::exercise-19')==q['entire_original_exercise']
 assert sha(ROOT/q['source'])==q['source_sha256_before']
 for item in q['prior_component_packets_and_independent_peers']:check(item)
 names=[]
 for row in q['proof_rows']:
  source=check(row['proof_source']);snapshot=check(row['original_source_snapshot'])
  assert source.read_bytes()==snapshot.read_bytes();actual=read(check(row['actual_standalone_record']))
  assert actual['actual_exit_code']==0 and actual['source_sha256_after']==sha(source)
  assert actual['actual_command']==['lake','env','lean',str(snapshot)]
  assert actual['cwd']==str(ROOT/'verification/lean') and sha(check(row['raw_log']))==actual['raw_log_sha256']
  assert sha(check(row['original_runner']))==actual['runner_sha256']
  names.extend(re.findall(r'^theorem ([A-Za-z0-9_]+)',source.read_text(),re.M))
 assert len(names)==q['public_theorem_count']==37
 for primary in q['primary_context_actually_read']:check(primary)
 manifest=read(check(q['protected_selected22_sources']['manifest']));assert len(manifest['proof_files'])==1113
 for name,row in manifest['proof_files'].items():assert sha(ROOT/name)==row['sha256']
 # The three exact semantic replacements were fully read against the independent37 component bodies.
 a,c,d=[row['after'] for row in q['replacements']]
 assert '\\ln1000/\\ln(20/19)\\approx134.7' in a and 'Under the convex scenario-program assumptions' in a
 assert '=6.9078/0.051293=134.7' not in a
 assert '$1-e^{-0.0928}\\approx9\\%$' in c and '=e^{-0.0928}\\approx0.911' in c
 assert 'For a fixed' in d and 'one fresh independent batch' in d and 'acceptance' in d and 'implies' in d and 'repeated validation attempts need a separate failure budget' in d
 sys.path.insert(0,str(ROOT/'book'))
 frozen=ROOT/'reports/full-coverage/checkpoint-22'
 for name,digest in old['source_sha256'].items():assert sha(frozen/name)==digest
 simulations=[simulate(q,old,frozen,'source48-frozen22')]
 current=read(ROOT/'book/coverage/inventory.json');current_sha=sha(ROOT/'book/coverage/inventory.json')
 assert current_sha=='67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99'
 assert current['counts']==old['counts']
 assert next(r for r in current['exercises'] if r['key']=='lyapunov-mpc.html::exercise-19')==q['entire_original_exercise']
 for name,digest in current['source_sha256'].items():assert sha(ROOT/name)==digest
 simulations.append(simulate(q,current,ROOT,'source49-observed-current'))
 assert sha(ROOT/'book/coverage/inventory.json')==current_sha and sha(ROOT/q['source'])==q['source_sha256_before']
 result={'status':'passed_independent_proposal_only_scenario11_4_precision_semantics_and_two_fresh_full_parsers_future23','reviewed_by':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'original_proposal_prepared_at_utc':q['prepared_at_utc'],'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__)),'errors':[],'source':q['source'],'source_sha256_before':q['source_sha256_before'],'proposed_source_sha256_after':q['proposed_source_sha256_after'],'exact_original_replacement_paragraphs':q['replacements'],'semantic_decisions':[{'source_unit_key':q['replacements'][0]['source_unit_key'],'proposal_text_approved':True,'reason':'Each log/ratio approximation is genuinely certified, the exact logarithmic iff and least integer135 are retained. Actual convex scalar support count holds under an attained feasible optimizer and the primary scenario assumptions. The generic missed-region/risk explanation remains explicitly primary-attributed: the random optimizer-dependent region is not assigned the fixed-threshold independent all-miss probability by this review.'},{'source_unit_key':q['replacements'][1]['source_unit_key'],'proposal_text_approved':True,'reason':'Both logarithmic ceilings and rational exponent are correct. Each finite decimal is marked approximate, and the actual exact exponential defines the Hoeffding confidence lower bound. The text retains the distinction from actual procedure confidence.'},{'source_unit_key':q['replacements'][2]['source_unit_key'],'proposal_text_approved':True,'reason':'Fixed controller, one fresh independent batch and normalized true credible-posterior Bernoulli stability law give probability≥.99 of the accepted-test implication. The true full-posterior lower bound .8835 implies the stated .88. This asserts neither conditional-on-accept confidence nor repeated-until-pass control, and does not construct/calibrate the GP posterior or prove nonlinear stability.'}],'original37_component_packets_peers_and_times_unchanged':q['prior_component_packets_and_independent_peers'],'original37_actual_standalone_sources_records_rawlogs_snapshots_runners':q['proof_rows'],'actual_independent_full_parser_runs':simulations,'original_source48_inventory':q['original_inventory'],'observed_current_source49_inventory':{'file':'book/coverage/inventory.json','sha256':current_sha},'only_changed_exercise_and_three_literals':q['expected_changed_text_keys'],'Root_monitoring49_bytes_retained_in_current49_simulation':True,'all1113_selected22_sources_exact':True,'whole_corrected_exercise_approved':False,'whole_material_unit_promotions':[],'working_HTML_inventory_or_ledgers_written':False,'coverage_complete':False,'limits':['Only the proposal text changes are approved. The general optimized scenario-risk probability theorem remains primary-attributed and formally pending; the fixed-threshold all-miss model is not substituted for it.','The posterior model and genuine common independent test law are explicit assumptions; no GP construction, nonlinear-system stability or repeated-until-pass theorem is inferred.','The proposal was prepared against immutable source48. This independent checker freshly ran all29-page parsers against both frozen22/source48 and observed current49, retaining Root Monitoring49 correction exactly. Root49 apply completion is not inferred from current files.','No current HTML, inventory, ledger, canonical proof, coverage decision, aggregate23 or deployment is written or claimed. Only unique TMP simulations/checker/review files are written.']}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'review':str(OUT),'review_sha256':sha(OUT),'fresh29_page_parsers':2,'changed_text_keys':q['expected_changed_text_keys']}))
if __name__=='__main__':
 try:main()
 except Exception:
  message=traceback.format_exc()
  if not FAIL.exists():
   with FAIL.open('x') as f:f.write(json.dumps({'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__)),'failure':message},indent=2)+'\n')
  sys.stderr.write(message);sys.exit(1)
