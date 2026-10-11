from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,traceback,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp');START=datetime.now(timezone.utc).isoformat()
OUT=TMP/'monitoring-shifted-mean23-independent-foundations-components-review-v1.json';FAIL=TMP/'monitoring-shifted-mean23-independent-foundations-checker-failure-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
def check(r):
 p=path(r['file']);assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p
def main():
 assert not OUT.exists() and not FAIL.exists()
 source=TMP/'root-monitoring-shifted-mean23-trial4.lean';assert sha(source)=='23367dac7f0ad16b258a895ffeaa62dcc334b3291646458760fb20f58fdc4c46'
 text=source.read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',text)
 names=['SafeLearning.CompleteMonitoringShiftedMean23.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)];assert len(names)==2
 history=[]
 for n,exitcode in [(1,1),(2,1),(3,0),(4,0)]:
  stem=TMP/f'root-monitoring-shifted-mean23-trial{n}';p=stem.with_suffix('.json');r=read(p);snapshot=stem.with_suffix('.lean');log=stem.with_suffix('.log');runner=TMP/f'root-monitoring-shifted-mean23-trial{n}-run.py'
  assert r['exit_code']==exitcode and r['command']==['lake','env','lean',str(snapshot)] and r['source_sha256']==sha(snapshot) and r['log_sha256']==sha(log)
  runtext=runner.read_text();assert "cwd='/home/oxrexkevin/SafetyBased/verification/lean'" in runtext
  assert bool(re.search(r'\berror(?:\(|:)',log.read_text()))==(exitcode!=0)
  history.append({'record':ref(p),'entire_original_actual_record':r,'source':ref(snapshot),'raw_log':ref(log),'actual_runner':ref(runner),'source_identity_scope':'Original record captures the source after execution; no separate before-run hash is claimed.'})
 assert history[3]['raw_log']['sha256']=='e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'
 prior=TMP/'monitoring-mean-prefix23-independent-foundations-review-v1.json';assert sha(prior)=='0fddc11cb46f97e2a7d9989ae017296e32cc5ac1bafd5ee8fd40f98158e94e90';old=read(prior)
 for n,h in old['all_exact_reference_bytes_sha256'].items():assert sha(path(n))==h
 dependency=ROOT/'verification/lean/SafeLearning/CompleteMonitoringDeterministicPath23.lean';assert sha(dependency)==old['proof_source']['sha256']
 readiness=ROOT/'book/coverage/checks/future23-monitoring/root-monitoring-shift23-canonical-readiness-v1.json';q=read(readiness)
 assert check(q['source']).read_bytes()==source.read_bytes()==check(q['source_snapshot']).read_bytes() and q['public_theorem_count']==2
 paired=[]
 for row in q['actual_canonical_pair']:
  r=read(check(row));log=check(row['log']);assert r['exit_code']==row['actual_exit_code']==0 and r['source_sha256_before']==r['source_sha256_after']==sha(source)
  assert r['log_sha256']==sha(log) and r['source_unchanged'] is True
  paired.append({'reference':row,'entire_original_actual_record':r})
 for n,row in q['original_TMP_byte_copies'].items():assert check(row).read_bytes()==Path(n).read_bytes()
 invpath=ROOT/'book/coverage/inventory-after-correction49.json';assert sha(invpath)=='67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99';inv=read(invpath)
 literal=next(r for r in inv['material_source_units'] if r['key']=='cmdp.html::node-1138');assert sha(ROOT/literal['source'])==literal['source_sha256']
 manifestpath=ROOT/'reports/full-coverage/checkpoint-22-manifest.json';manifest=read(manifestpath);assert len(manifest['proof_files'])==1113
 for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 reasons=[{'name':names[0],'approved':True,'hypotheses':['u is an arbitrary real sequence; K is one fixed natural index shift; its actual Cesaro averages converge to the finite realL.'],'reason':'The exact sum identity subtracts the firstK terms from the sum throughN+K. For positiveN the shifted mean equals(1+K/N) times the original(N+K) mean minus the fixed prefix sum/N. Both correction factors have their actual limits; no uniform boundedness or per-term convergence is assumed.','missing_clauses':[]},{'name':names[1],'approved':True,'hypotheses':['u,v are real sequences; K is fixed; for every naturaln, u(n+K)=v(n).'],'reason':'The forward implication is the generic fixed-shift theorem. For the reverse, a zero-prefixedv sequence has exact mean equal to its fixed prefix sum/N plus(1-K/N) times the(N-K) mean ofv forN>K. Nat subtraction tends to infinity. The existing independently approved aligned-prefix theorem transfers this limit to arbitraryu with the same tail. This proves an equivalence for the original finite real limitL.','missing_clauses':[]}]
 result={'status':'passed_independent_two_body_shifted_Cesaro_mean_components_future23','reviewer':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'errors':[],'proof_source':ref(source),'full_source_and_both_public_bodies':text,'public_theorem_names':names,'per_component_decisions':reasons,'all_actual_failed_and_passing_unique_trials':history,'unchanged_previous29_source_and_aligned_prefix_peer':{'reference':ref(prior),'entire_original_body':old},'actual_canonical_readiness':ref(readiness),'actual_canonical_source':q['source'],'actual_canonical_pair':paired,'original_TMP_byte_copies':q['original_TMP_byte_copies'],'actual_source49_inventory':ref(invpath),'exact_relevant_whole_current49_literal':literal,'all1113_selected22_proof_sources_exact':True,'whole_source49_unit_or_exercise_approved':False,'coverage_complete':False,'limits':['This closes only the generic fixed shifted-tail/time-average component of the finite initial route phrase.','No physical admissibility, projected-price preservation, uniform controller convergence or arbitrary variable-length prefix theorem is inferred.','All prior29 semantic body/times and original histories remain exact. Canonical executions are bound as genuine compiler evidence; aggregate23/selection/whole(b) approval remain separate.','Only new TMP checker/review files are written. Current HTML/inventory/four ledgers and selected1113 proof sources are not edited.']}
 with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'review':ref(OUT),'public_theorems':2,'whole_unit_approved':False}))
if __name__=='__main__':
 try:main()
 except Exception:
  msg=traceback.format_exc()
  if not FAIL.exists():
   with FAIL.open('x') as f:f.write(json.dumps({'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'failure':msg},indent=2)+'\n')
  sys.stderr.write(msg);sys.exit(1)
