from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future28-foundations/owner29-approved-eight-scope-plan-v1';OUT=Path('/tmp/foundations-owner29-approved-eight-scope-plan-v1.json');assert not OUT.exists() and not D.exists();D.mkdir(parents=True)
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
start=datetime.now(timezone.utc).isoformat()
def p(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def read(n):return json.loads(p(n).read_bytes())
def ref(n):return {'file':str(n),'sha256':sha(n),'bytes':p(n).stat().st_size}
known={};closed={};aliases={}
CATALOGS=['book/coverage/checks/future29-foundations/innerproduct14-full-independent-modules-v1/original-closed-byte-aliases-v1.json','book/coverage/checks/future29-foundations/normcomparison8-independent-modules-v1/foundations-normcomparison8-whole184-independent-modules29-peer-v1.json','book/coverage/checks/future28-foundations/source64-exact-norm-uses-qualifiers29-v1/original-closed-byte-aliases-v1.json','book/coverage/checks/future28-foundations/original-basics-source61-three-actual-countermodels-independent-modules28-v1/original-closed-byte-aliases-v1.json','book/coverage/checks/future29-core/source62-four-components-independent-modules-v1/source62-four-components-independent-full-literal-modules29-peer-v1.json']
for n in CATALOGS:
 v=read(n)
 for key in ['original_to_durable','original_byte_aliases','original_closed_byte_aliases']:
  if isinstance(v.get(key),dict):
   for old,r in v[key].items():
    if isinstance(r,dict) and isinstance(r.get('file'),str) and isinstance(r.get('sha256'),str):
     assert old not in known or known[old]['sha256']==r['sha256'];known[old]=r

def normalize(n,h=None):
 n=str(n); h=h or sha(n)
 if n in aliases:assert aliases[n]['sha256']==h;return aliases[n]
 q=p(n);assert q.is_file() and sha(n)==h,n
 if n in known:
  r=known[n];assert r['sha256']==h and sha(r['file'])==h
 elif q.is_relative_to(R):
  rel=q.relative_to(R).as_posix();snapshot='reports/full-coverage/checkpoint-28/'+rel
  if p(snapshot).is_file() and sha(snapshot)==h:r={'file':snapshot,'sha256':h}
  else:r={'file':rel,'sha256':h}
 else:
  assert q.is_relative_to('/tmp') and q.stat().st_size<2000000,(n,q.stat().st_size)
  t=D/'original-by-sha256'/h/q.name;t.parent.mkdir(parents=True,exist_ok=True)
  if not t.exists():t.write_bytes(q.read_bytes())
  assert sha(t)==h;r={'file':t.relative_to(R).as_posix(),'sha256':h}
 aliases[n]=r;closed[r['file']]=r['sha256'];return r

def peer(n):
 v=read(n);assert v['errors']==[] and v['status'].startswith('passed_independent_')
 return normalize(n),v
IP='book/coverage/checks/future29-foundations/innerproduct14-full-independent-modules-v1/foundations-innerproduct14-three-whole-literals-independent-modules29-peer-v1.json'
NU='/tmp/foundations-norm-csuses24-independent-applied-full-source-review28-v1.json'
NC='book/coverage/checks/future29-foundations/normcomparison8-independent-modules-v1/foundations-normcomparison8-whole184-independent-modules29-peer-v1.json'
B3='book/coverage/checks/future28-foundations/original-basics-source61-three-actual-countermodels-independent-modules28-v1/basics-source61-countermodels3-independent-modules28-closed-v1.json'
T4='book/coverage/checks/future29-core/source62-four-components-independent-modules-v1/source62-four-components-independent-full-literal-modules29-peer-v1.json'
S64='book/coverage/checks/future28-foundations/source64-exact-norm-uses-qualifiers29-v1/source64-narrow-exact-wording-and-full29-parser-approved-closed-v1.json'
ipr,ipv=peer(IP);nur,nuv=peer(NU);ncr,ncv=peer(NC);b3r,b3v=peer(B3);t4r,t4v=peer(T4);s64r,s64v=peer(S64)
for n,v in [(IP,ipv),(NU,nuv),(NC,ncv),(B3,b3v),(T4,t4v),(S64,s64v)]:
 for field in ['required_evidence_artifacts_sha256','closed_evidence_sha256']:
  for key,h in v.get(field,{}).items():normalize(key,h)
for n in CATALOGS:normalize(n)
NU_REQUEST='/tmp/foundations-norm-csuses24-four-full-literals-review28-v1.json';normalize(NU_REQUEST)
for r in read(NU_REQUEST)['complete_selected_dependencies']:
 if isinstance(r,dict) and 'file' in r:normalize(r['file'],r['sha256'])
SOURCE64_PROP='/tmp/foundations-norm-uses-source64-proposal29-v1/foundations-norm-uses-source64-proposal29-v1.json';sp=read(SOURCE64_PROP);normalize(SOURCE64_PROP)
old_inv='reports/full-coverage/checkpoint-28/book/coverage/inventory.json';inv=read(old_inv);normalize(old_inv)
owner='reports/full-coverage/checkpoint-28/book/coverage/foundations.json';normalize(owner)
cor='reports/full-coverage/checkpoint-28/book/coverage/material-corrections.json';normalize(cor)
units={x['key']:x for x in inv['material_source_units']};proposed141=sp['entire_current_and_proposed_literal_records']['primer-linalg.html::node-141']['entire_proposed']
assert nuv['whole147_149_152_approved'] is True and nuv['whole_current141_approved'] is False
S64_ORIGINAL='/tmp/foundations-source64-independent-applied-full-wording-parser-review29-v1.json';sv=read(S64_ORIGINAL);assert 'all seven full bodies' in sv['prospective_corrected141_whole_association'];normalize(S64_ORIGINAL)

sources=[]
specs=[('innerproduct14','/tmp/CompleteFoundationsLiteralInnerProductWholeUnits28-draft-v5.lean','CompleteFoundationsLiteralInnerProductWholeUnits29.lean',14,['/tmp/foundations-literal-innerproduct14-owner28-trial'+str(i)+'.json' for i in range(1,4)],ipr,['primer-linalg.html::node-'+str(i) for i in [126,128,136]],'whole_literal'),('norm17','/tmp/CompleteFoundationsLiteralNormWholeUnits28-draft-v6.lean','CompleteFoundationsLiteralNormWholeUnits29.lean',17,['/tmp/foundations-literal-norm17-owner28-trial'+str(i)+'.json' for i in range(1,5)],nur,['primer-linalg.html::node-'+str(i) for i in [147,149,152]],'whole_literal'),('uses7','/tmp/CompleteFoundationsLiteralCauchySchwarzUses28-draft-v5.lean','CompleteFoundationsLiteralCauchySchwarzUses29.lean',7,['/tmp/foundations-literal-cauchy-schwarz-uses7-owner28-trial'+str(i)+'.json' for i in range(1,5)],nur,['primer-linalg.html::node-141'],'whole_corrected_literal_association_requires_actual64_and_new_canonical_pairs'),('normcomparison8','/tmp/CompleteFoundationsLiteralNormComparisonProof29-draft-v3.lean','CompleteFoundationsLiteralNormComparisonProof29.lean',8,['/tmp/foundations-literal-norm-comparison8-owner28-trial'+str(i)+'.json' for i in range(1,4)],ncr,['primer-linalg.html::node-184'],'whole_literal'),('basics_countermodels3','/tmp/CompleteFoundationsBasicsDegenerateCountermodels28-draft-v3.lean','CompleteFoundationsBasicsDegenerateCountermodels29.lean',3,['/tmp/foundations-basics-degenerate-countermodels3-source60-28-trial'+str(i)+'.json' for i in range(1,4)],b3r,['primer-basics.html::node-'+str(i) for i in [1029,1031,1142]],'countermodel_components_only'),('timing_relu4','/tmp/CompleteFoundationsTimingReLUCancellationCountermodels28-draft-v1.lean','CompleteFoundationsTimingReLUCancellationCountermodels29.lean',4,['/tmp/foundations-source62-countermodels4-owner28-trial1.json'],t4r,['primer-optimization.html::node-200','primer-optimization.html::node-202'],'components_only')]
for group,source,dest,count,trialnames,pr,keys,scope in specs:
 text=p(source).read_text();ds=declarations(text);ns=[d['name'] for d in ds if d['kind'] in ('theorem','lemma')];assert len(ns)==count
 target='verification/lean/SafeLearning/'+dest;assert not p(target).exists()
 history=[]
 for i,n in enumerate(trialnames):
  a=read(n);assert type(a['actual_exit_code']) is int and a['actual_exit_code']==(0 if i==len(trialnames)-1 else 1)
  assert a.get('protection_errors',[])==[]
  snapshot=a['source_snapshot'];log=a['raw_log'];assert sha(snapshot)==a['source_snapshot_sha256']==a['source_sha256_before']==a['source_sha256_after'];assert sha(log)==a['raw_log_sha256']
  history.append({'actual':normalize(n),'raw_log':normalize(log,a['raw_log_sha256']),'source_snapshot':normalize(snapshot,a['source_snapshot_sha256']),'actual_exit_code':a['actual_exit_code'],'warning_count':len(re.findall(r'^.*\.lean:\d+:\d+: warning:',p(log).read_text(),re.M)),'started_at_utc':a['started_at_utc'],'finished_at_utc':a['finished_at_utc'],'elapsed_seconds':a['elapsed_seconds'],'historical_runner':normalize(a['original_actual_runner']['file'],a['original_actual_runner']['sha256']) if 'original_actual_runner' in a else None,'historical_context':normalize(a['actual_verified_owner28_context']['file'],a['actual_verified_owner28_context']['sha256']) if 'actual_verified_owner28_context' in a else None,'historical_record_body_and_context_unchanged':True})
 assert history[-1]['source_snapshot']['sha256']==sha(source)
 sources.append({'group':group,'exact_original_tmp_source':ref(source),'durable_exact_source':normalize(source),'suggested_new_canonical_destination':target,'public_theorem_count':count,'public_theorem_names':ns,'full_public_declaration_index':ds,'original_genuine_trial_chain':history,'successful_original_standalone_tmp_execution':history[-1]['actual'],'independent_full_source_correspondence_peer':pr,'scope':scope,'physical_literal_keys':keys,'new_canonical_standalone_and_named_pair_execution_pending':True,'canonical_destination_written':False})
# Narrow maps expose the direct source clauses; broader nearby claims are absent.
by={s['group']:s for s in sources};material=[]
for group,keys in [(x[0],x[6]) for x in specs[:4]]:
 s=by[group]
 for key in keys:
  unit=proposed141 if key.endswith('node-141') else units[key]
  if group=='innerproduct14':
   selected=[n for n in s['public_theorem_names'] if (('parabola' in n or 'cauchy_schwarz' in n or 'equality' in n or 'three_source_axioms' in n) if key.endswith('136') else any(t in n for t in ['every_source_axiom','standard_euclidean','weighted_inner','weighted_length','diagonal_weights']))]
   decision=next(d for d in ipv['individual_full_literal_decisions'] if d['source_unit_key']==key);reason=decision['full_clause_reason'];assert decision['entire_literal_approved'] and decision['missing_clauses']==[]
  elif group=='norm17':
   names=s['public_theorem_names'];selected=names if key.endswith('152') else [n for n in names if not any(t in n for t in ['printed_vector','two_dimensional','printed_nesting'])]
   decision=next(d for d in nuv['material_units'] if d['key']==key);reason=decision['reason'];assert decision['whole_unit_approved'] and decision['missing_clauses']==[]
  elif group=='uses7':selected=s['public_theorem_names'];reason=sv['prospective_corrected141_whole_association']
  else:
   selected=s['public_theorem_names'];decision=ncv['individual_full_literal_decisions'][0];reason=decision['full_clause_reason'];assert decision['entire_literal_approved'] and decision['missing_clauses']==[]
  material.append({'inventory_key':key,'proof_group':group,'expected_post_source64_source':unit['source'],'expected_post_source64_source_sha256':sp['proposed_source']['sha256'],'expected_literal_text_sha256':unit['text_sha256'],'whole_literal_independent_review_approved':True,'whole_peer':s['independent_full_source_correspondence_peer'],'additional_corrected_literal_association_peer':normalize(S64_ORIGINAL) if group=='uses7' else None,'direct_new_named_declarations':selected,'full_clause_correspondence_reason':reason,'missing_clauses':[],'current_owner_status_changed':False,'current64_rebase_and_new_native_canonical_pairs_required':True})
assert len(material)==8 and len({m['inventory_key'] for m in material})==8
bib='book/coverage/checks/future28-core/bibliography8-independent-modules28-v1/foundations-bibliography8-independent-full-literal-classification-modules28-peer-v1.json';bv=read(bib);normalize(bib)
record={'status':'prepared_exact_approved_foundations_owner29_eight_math_units_scope_plan_only','author':'/root/foundations_recovery28','started_at_utc':start,'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'immutable_owner28_source60_foundations':normalize(owner),'immutable_original_source60_inventory':normalize(old_inv),'immutable_original_source60_corrections':normalize(cor),'prospective_source64_wording_and_association_closure':s64r,'exercise_scope':[],'material_scope':material,'proof_source_scope':sources,'scope_counts':{'whole_math_units':8,'whole_math_proof_sources':4,'whole_math_public_theorems':46,'optional_component_only_sources':2,'optional_component_only_public_theorems':7,'all_six_exact_sources_public_theorems':53,'separate_individually_approved_nonformal_bibliography_rows':8},'separate_nonformal_editorial_scope':{'physical_literal_keys':['primer-basics.html::node-'+str(i) for i in [1648,1654,1660,1666,1672,1678,1684,1690]],'proposed_status':'not_a_formal_claim','individual_full_literal_primary_reference_peer':normalize(bib),'mathematical_claims_promoted':False,'live_owner_changes':False},'preservation_requirements':['Preserve all119 complete exercises and all1133 prior proved material claims, proof metadata, semantic reviews, native commands/body times and historical failures exactly.','All original TMP pass records retain source60/owner28 or source60/owner27 context; never relabel them as source64 or canonical execution.','Use exactly these source bytes for new canonical standalone/named pairs after Source61–64 actual application and new runner context.','Owner29 identity rebase, canonical pairs and final full literal mapping review must precede any current whole status change.','Countermodel3 and timing/ReLU4 remain component-only; no whole1029/1031/1142/200/202 approval is inferred.','Unit141 association is with exact corrected64 literal only; prior24 current141 whole-pending decision remains exact historical evidence.'],'original_byte_aliases':aliases,'required_evidence_artifacts_sha256':closed,'canonical_owner_source_selection_or_publication_mutated':False,'owner_candidate_prepared':False,'coverage_complete':False}
OUT.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n');f=D/'foundations-owner29-approved-eight-math-units-six-source-scope-plan-v1.json';f.write_bytes(OUT.read_bytes());print(json.dumps({'scope_plan':ref(f.relative_to(R).as_posix()),'counts':record['scope_counts'],'closed_refs':len(closed),'new_original_byte_copies':len(list((D/'original-by-sha256').glob('*/*')))}))
