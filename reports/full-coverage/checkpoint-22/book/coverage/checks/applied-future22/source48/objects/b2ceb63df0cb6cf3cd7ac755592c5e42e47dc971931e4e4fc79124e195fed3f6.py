from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
rp='/tmp/applied-nine-elementary-material21-independent-review-request-v1.json';req=read(rp);assert sha(rp)=='9ca8df6bcbb3458262eb6b3ccdadf4f5062f7bf24f609b9f85e2195ce2498ef6'
iv=read(req['inventory']);assert sha(req['inventory'])==req['inventory_sha256']==sha('book/coverage/inventory.json');units={r['key']:r for r in iv['material_source_units']};names=set();executions=[];retained=[]
for p in req['proofs']:
 assert sha(p['source'])==p['source_sha256'] and Path(p['source']).read_text()==p['source_text']
 for ref in p.get('new_actual_executions',[]):
  assert sha(ref['file'])==ref['sha256'];rec=read(ref['file']);assert rec==ref['record'];assert rec['exit_code']==0 and rec['source_sha256_before']==rec['source_sha256_after']==p['source_sha256'];assert sha(rec['log'])==rec['log_sha256'];assert sha(rec['source_snapshot'])==rec['source_snapshot_sha256']==p['source_sha256'];executions.append(dict(file=ref['file'],sha256=ref['sha256'],exit_code=0,source=p['source'],source_sha256=p['source_sha256'],log=rec['log'],log_sha256=rec['log_sha256'],original_started_at_utc=rec['started_at_utc'],original_finished_at_utc=rec['finished_at_utc']))
 if 'retained_actual_selected20_evidence' in p:
  evidence=p['retained_actual_selected20_evidence'];assert evidence['sha256']==p['source_sha256']
  for f,h in evidence['evidence_sha256'].items():assert sha(f)==h,(f,h)
  retained.append(dict(source=p['source'],source_sha256=p['source_sha256'],retained_actual_selected20_evidence=evidence))
rows=[]
reasons=[
'The complete literal is the set partition identity. The arbitrary outcome-space theorem establishes both event union complement equals the universe and disjointness; no finite-space or event-measurability assumption is needed for this set identity.',
'The diagnostic calculation and strict comparison are read in the displayed sign-variable model. The actual normalized finite model gives the stated moments, zero covariance and a concrete failure of independence; the genuine square-integrable independent-variable theorem proves the forward covariance implication. No converse is inferred.',
'The actual fair-die conditional probability uses the normalized PMF and the nonzero event of outcomes 4, 5 and 6. The new theorem proves the exact three atoms and their equal conditional masses 1/3, with zero mass outside that event.',
'The two copies of each of 50 observations have exactly the same sample average as the original 50 observations. Under the source independent Bernoulli assumptions the actual mean and variance identities distinguish 50 distinct samples from 100 independent samples; the copied records acquire no independence.',
'This is the diagnostic instruction to find fixed points by equating current and next state; it asserts no particular solution or equilibrium value in this unit.',
'The actual source trajectory 3*exp(-2*t) has its genuine derivative, including the chain-rule factor -2, for every real time. This approves only the displayed calculation.',
'This is a calculation instruction to weight a reward by the probability of choosing its action. The instruction states no separate numerical return or optimal-policy theorem.',
'The displayed ordinary geometric reward series has ratio 1/2 and sum 4. The actual finite partial sums, convergence and infinite sum provide the factor-two reasoning on its stipulated positive discounted model.',
'The source bilinear network/output is differentiated with the other real argument held fixed. Both genuine one-variable derivative identities prove the stated partial calculations; no differentiability of arbitrary functions or broader backpropagation claim is inferred.'
]
for r,reason in zip(req['material_units'],reasons):
 u=r['entire_inventory_record'];assert units[u['key']]==u and sha(u['source'])==u['source_sha256'];context=r['complete_context'];text='\n'.join(Path(context['source']).read_text().splitlines()[context['start_line']-1:context['end_line']]);assert context['text'].rstrip('\n')==text
 status=r['proposed_material_status'];assert status in ['proved','not_a_formal_claim'];assert not r['missing_clauses'];assert bool(r['lean_declarations'])==(status=='proved');rows.append(dict(source_unit_key=u['key'],unit_text_sha256=u['text_sha256'],source=u['source'],source_sha256=u['source_sha256'],line=u['line'],locator=u['locator'],exact_current48_inventory_record=u,material_status=status,review_status='independent_full_literal_review_passed',per_unit_reason=reason,hypotheses=r['hypotheses'],lean_declarations=r['lean_declarations'],missing_clauses=[],complete_context_sha256=hashlib.sha256(context['text'].encode()).hexdigest(),original_proposed_row=r))
manifest=read('reports/full-coverage/checkpoint-20-manifest.json')
for p,r in manifest['proof_files'].items():assert sha(p)==r['sha256'],p
for p,h in manifest['frozen_inputs_sha256'].items():assert sha(Path(manifest['snapshot'])/p)==h,p
out=dict(schema_version=1,status='independent_complete_literal_elementary_nine_material_review_passed',reviewer='/root/foundations_next',reviewed_at_utc=datetime.now(timezone.utc).isoformat(),review_request=rp,review_request_sha256=sha(rp),inventory=req['inventory'],inventory_sha256=req['inventory_sha256'],material_units=rows,complete_proof_sources_read={p['source']:p['source_sha256'] for p in req['proofs']},actual_new_source_execution_records=executions,retained_actual_selected20_sources_and_evidence=retained,counts=dict(individual_complete_literals=9,whole_proved=7,individually_nonformal=2,whole_pending=0),protected20=dict(selected_proof_sources=len(manifest['proof_files']),frozen_inputs=len(manifest['frozen_inputs_sha256']),all_exact=True),limits=['Full literal/context and all seven complete proof sources were individually read before this exact check. Only these nine material units are approved; neighboring questions, answers and physical models retain their separate coverage.','Two genuine new execution records are checked with their original times and honestly nonempty warning logs. Retained sources use their genuine passing selected20 aggregate/evidence; no fresh standalone run is invented.','No source HTML, owner21 ledger/helper/offer or prior proof/evidence/review was modified by this peer.'])
p='book/coverage/checks/applied-future21/applied-nine-elementary-material21-independent-foundations-source-review-v1.json';assert not Path(p).exists();Path(p).write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(p,sha(p),out['counts'])
