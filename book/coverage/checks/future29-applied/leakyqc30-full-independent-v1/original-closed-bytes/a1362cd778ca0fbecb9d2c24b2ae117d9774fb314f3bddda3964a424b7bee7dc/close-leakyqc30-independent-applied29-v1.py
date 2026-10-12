from pathlib import Path
import json,hashlib
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future29-applied/leakyqc30-full-independent-v1';D.mkdir(parents=True,exist_ok=True)
P=D/'leakyqc30-full-source-independent-applied29-peer-v1.json';assert not P.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rootref(p):return {'file':str(Path(p).relative_to(R)),'sha256':sha(p)}
req=R/'book/coverage/checks/modules-future29/leaky-qc30-and-source63-v1/modules-leaky-qc30-full-scope-independent-review-request29-v1.json';request=json.loads(req.read_text());find=Path('/tmp/leakyqc30-independent-applied-findings29-v2.json');f=json.loads(find.read_text())
assert f['errors']==[] and json.loads(Path('/tmp/leakyqc30-independent-applied-actual29-v2.json').read_bytes())['actual_exit_code']==0
aliases={};closure=dict(request['required_evidence_artifacts_sha256'])
def close(original,h=None):
 o=Path(original);h=h or sha(o)
 if str(o) in request['original_exact_byte_aliases']:
  q=request['original_exact_byte_aliases'][str(o)];p=R/q['file'];assert sha(p)==h;aliases[str(o)]=q;closure[q['file']]=h;return q
 if o.is_relative_to(R) and o.resolve().is_relative_to(R):
  assert sha(o)==h;q=rootref(o);closure[q['file']]=h;return q
 p=D/'original-closed-bytes'/h/o.name;p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert sha(p)==h
 else:p.write_bytes(o.read_bytes())
 assert sha(p)==h;q=rootref(p);aliases[str(o)]=q;closure[q['file']]=h;return q
for n,h in f['closed_evidence_sha256'].items():close(n,h)
for n in ['/tmp/check-leakyqc30-independent-applied29-v2.py','/tmp/run-leakyqc30-independent-applied29-v2.py','/tmp/leakyqc30-independent-applied-actual29-v2.json','/tmp/leakyqc30-independent-applied-actual29-v2.log',str(find),__file__]:close(n)
cat=D/'original-closed-byte-aliases-v1.json';assert not cat.exists();cat.write_text(json.dumps({'status':'exact_original_independent_reader_byte_aliases','original_closed_byte_aliases':aliases},indent=2)+'\n');closure[rootref(cat)['file']]=sha(cat)
peer={k:v for k,v in f.items() if k!='closed_evidence_sha256'}
peer.update({'status':'passed_independent_full_leakyqc30_source_and_prospective_source63_semantic_review','request':rootref(req),'proof_source':close(request['proof_source']['file'],request['proof_source']['sha256']),'actual_reader':close('/tmp/leakyqc30-independent-applied-actual29-v2.json'),'actual_finalizer':close('/tmp/leakyqc30-independent-applied-actual29-v2.json'),'original_entire_independent_findings_body_and_time':close(str(find)),'original_closed_byte_aliases':aliases,'original_closed_byte_alias_catalog':rootref(cat),'required_evidence_artifacts_sha256':closure,'closed_evidence_sha256':closure,'peer_compaction_preserves_all_decisions_and_original_times':True})
P.write_text(json.dumps(peer,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'peer':rootref(P),'bytes':P.stat().st_size,'closure_refs':len(closure),'alias_refs':len(aliases)}))
