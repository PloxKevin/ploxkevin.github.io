"""Bind the original independently approved Core22 candidate in a new final offer."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,copy
ROOT=Path(__file__).resolve().parents[4]
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
old='book/coverage/checks/future22-monitoring/core-audit22-candidate-source48-additions-v1.json'
assert sha(old)=='df48ff0d78c10767115ad7cbf3d7132fe168f821b0d2aff85cd595651d53370d'
peer='book/coverage/checks/future22-monitoring/core22-candidate-mapping-independent-applied-confirmation-v1.json'
assert sha(peer)=='fe8a13fd46153766ceedcbc68ac20cb194ef1949af8be2b98449ad75512b503c'
x=read(old);p=read(peer);assert 'passed' in p['status'] and not p.get('errors')
assert sha(x['mapped_ledger'])==x['mapped_ledger_sha256']
assert sha(x['actual_builder'])==x['actual_builder_sha256'];assert read(x['actual_builder'])['actual_exit_code']==0
for n,h in x['review_sha256'].items():assert sha(n)==h
for n,h in x['baseline21_owner_assets'].items():assert sha(n)==h
for n,h in x['builder_sha256'].items():assert sha(n)==h
for n,e in x['proof_files'].items():
 assert sha(n)==e['sha256']
 for a,h in e['evidence_sha256'].items():assert sha(a)==h
for n,h in x['source_sha256'].items():assert sha(n)==h
result=copy.deepcopy(x)
result.update(status='exact_current48_reviewed_core_candidate_actual_paired_compiler_offer_ready_for_guarded_integration_requires_fresh_aggregate',finalized_at_utc=datetime.now(timezone.utc).isoformat(),original_candidate_offer=dict(file=old,sha256=sha(old)),independent_final_candidate_mapping_peer=dict(file=peer,sha256=sha(peer),original_review_time=p.get('reviewed_at_utc',p.get('checked_at_utc'))),finalization_helper=dict(file=str(Path(__file__).relative_to(ROOT)),sha256=sha(str(Path(__file__).relative_to(ROOT)))))
out=ROOT/'book/coverage/core-audit22-source48-additions-v1.json';assert not out.exists()
with out.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(file=str(out.relative_to(ROOT)),sha256=sha(str(out.relative_to(ROOT))),proof_file_count=result['proof_file_count'],public_theorem_count=result['local_theorem_count'],counts=result['counts'])))
