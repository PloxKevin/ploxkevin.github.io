from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def codes(d,w):
 keys=[k for k in ('exit_code','actual_exit_code','actual_runner_exit_code') if k in d]
 assert keys and all(type(d[k]) is int and d[k]==w for k in keys)
def archive(name,paths,scope):
 out=ROOT/'book/coverage/checks/future28-foundations'/name;catalog=out/'original-closed-byte-aliases-v1.json';assert not catalog.exists();aliases={}
 for p in dict.fromkeys(map(str,paths)):
  p=Path(p);h=sha(p);destination=out/h/p.name;destination.parent.mkdir(parents=True,exist_ok=True)
  if destination.exists():assert destination.read_bytes()==p.read_bytes()
  else:
   with destination.open('xb') as f:f.write(p.read_bytes())
  aliases[str(p)]={'file':str(destination.relative_to(ROOT)),'sha256':h}
 d={'status':'closed_exact_original_byte_aliases','archived_at_utc':datetime.now(timezone.utc).isoformat(),'original_closed_byte_aliases':aliases,'original_file_count':len(aliases),'scope':scope}
 with catalog.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
 print(json.dumps({'catalog':str(catalog.relative_to(ROOT)),'sha256':sha(catalog),'original_file_count':len(aliases)}))
held={n:sha(ROOT/n) for n in ('book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/foundations.json','reports/full-coverage/checkpoint-27-selection.json')}
assert held['book/coverage/inventory.json']=='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
mp=Path('/tmp/mpc-old-reference4-and-tightening4-independent-foundations28-v1.json');m=read(mp)
assert sha(mp)=='b470edba6661ba2e92a993fa835024dd5cc2991a448677187a31f719f4cc9823'
assert m['errors']==[] and m['component_count']==8 and m['whole_exercise18_approved'] is False and m['whole_material_units_approved'] is False
findings=read(m['original_findings']['file']);assert findings==m['entire_original_findings_body_and_time']
for k,v in findings.items():
 if k!='closed_evidence_sha256':assert m[k]==v,k
a=read(m['actual_reader_execution']['file']);codes(a,0)
assert a['actual_command']==['python3',m['actual_checker']['file']] and a['actual_workdir']==str(ROOT)
assert a['checker_sha256_before']==a['checker_sha256_after']==m['actual_checker']['sha256']
assert sha(a['raw_log'])==a['raw_log_sha256']==m['actual_reader_raw_log']['sha256']
assert json.loads(Path(a['raw_log']).read_text())['findings']==m['original_findings']
paths=[mp]+[Path(m[k]['file']) for k in ('actual_checker','actual_reader_execution','actual_reader_raw_log','actual_reader_runner','original_findings')]
for c in m['components']:
 assert len(c['component_decisions'])==4 and all(d['approved_component'] is True for d in c['component_decisions'])
 p=Path(c['request']['file']);assert sha(p)==c['request']['sha256'] and read(p)==c['entire_original_request_body_and_time'];paths.append(p)
 for original,r in read(p)['original_closed_byte_aliases'].items():assert sha(original)==sha(r['file'])==r['sha256'];paths.append(Path(original))
for n,h in m['closed_evidence_sha256'].items():assert sha(n)==h,n
archive('original-mpc-old-reference4-exact-tightening4-peer28-v1',paths,'Original eight component full-source semantic decisions, native reader0 and both requests retained, including all earlier raw failed/pass trials and prior review bodies/times. Whole18 remains pending the explicitly listed mathematical composition and adopted-domain/source correspondence obligations; no installed source/proofs/owners change.')

ap=Path('/tmp/foundations-allocation19-eight-full-literals-independent-applied-review28-v1.json');j=read(ap)
assert sha(ap)=='5d50809580ccdb91cef3f9323896201a719be9c616833513773edc2f285012ac'
assert j['errors']==[] and j['public_theorem_count']==19 and j['coverage_complete'] is False and j['parent_exercise_approval'] is False
assert len(j['material_units'])==8 and all(r['whole_source_unit_approved'] is True and r['missing']==[] for r in j['material_units'])
author=read(j['request']['file']);assert author==j['entire_original_author_packet_body_and_time'] and sha(j['request']['file'])==j['request']['sha256']
assert j['entire_prior17_claim_rows_unchanged']==author['current_existing_claims_unchanged']
actual=read(j['actual_independent_review']['file']);codes(actual,0)
assert actual['helper_sha256_before']==actual['helper_sha256_after'] and actual['protected_sha256_before']==actual['protected_sha256_after'] and actual['protection_errors']==[]
assert actual['actual_command']==['python3','/tmp/check-foundations-allocation19-eight-full-literals-independent-applied28-v2.py'] and actual['actual_workdir']==str(ROOT)
assert sha(actual['log'])==actual['log_sha256']
logged=json.loads(Path(actual['log']).read_text());obs=Path(logged['observations']);assert sha(obs)==logged['sha256'] and logged['whole_units']==8 and logged['public_theorems']==19
observations=read(obs)
for k,v in observations.items():assert j[k]==v,k
failure=read('/tmp/foundations-allocation19-eight-full-literals-independent-applied-actual28-v1.json');codes(failure,1)
assert failure==j['entire_original_independent_failure_body_and_time'] and failure['protection_errors']==[]
assert sha(failure['log'])==failure['log_sha256']
for n,h in j['closed_evidence_sha256'].items():assert sha(n)==h,n
for n,h in actual['protected_sha256_after'].items():assert sha(n)==h,n
paths=[ap,Path(j['request']['file'])]
paths +=[Path(n) for n in j['closed_evidence_sha256'] if n.startswith('/tmp/')]
archive('original-allocation19-eight-literal-independent-applied-peer28-v1',paths,'Eight complete literal decisions with full19-body author/source request and actual independent reader2 zero. Original reader1 newline-representation failure, genuine compiler1/2 source/raw records and five emitted pass warnings preserved without retiming. Model scope remains explicit; no whole parent exercise or installed proof/owner/aggregate promotion.')
for n,h in held.items():assert sha(ROOT/n)==h,n
print(json.dumps({'status':'passed_exact_original_mpc8_component_and_allocation8_whole_literal_evidence_closure','errors':[],'coverage_complete':False}))
