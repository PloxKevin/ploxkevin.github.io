"""Retain every frozen28 byte and original row with exact historical aliases."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re

BASELINE='reports/full-coverage/checkpoint-28-selection.json'
BASELINE_SHA='e954d6a3f22139ec6ebafbe4164c46f184fe5e2c672860c9fce5829f73424632'
MANIFEST='reports/full-coverage/checkpoint-28-manifest.json'
MANIFEST_SHA='7aae00ecb663b2b12d8938a26f8f67141abc20b94efb4fc9145ff7aab1290466'
AUDIT='reports/full-coverage/lean-checkpoint-28/verification-original.json'
AUDIT_SHA='7f12161869033e85af7927332eddee77cf62cdefbc5bb351150adec6b300adf8'

# Only these three old Source60 evidence retrieval paths changed at Source65.
HISTORICAL_EVIDENCE_ALIASES = {'book/coverage/material-corrections.json': {'file': 'reports/full-coverage/source-history/approved-corrections61-64-20261011/source60-owner28-original/book/coverage/material-corrections.json', 'sha256': '90097eba3c8b954074285ee91010745685c5f3e27cc99caf966c76d9ae7a1d81'}, 'book/coverage/inventory.json': {'file': 'reports/full-coverage/source-history/approved-corrections61-64-20261011/source60-owner28-original/book/coverage/inventory.json', 'sha256': '6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'}, 'SafeLearning/lipsdp.html': {'file': 'reports/full-coverage/source-history/approved-corrections61-64-20261011/source60-owner28-original/SafeLearning/lipsdp.html', 'sha256': 'c246dca4323f90c9d390c74dbd253872564627c225e24321b363fb2e4ffba5dc'}}

def retain(root,selected,extras,destination_name):
 root=Path(root)
 def safe(n):
  assert type(n) is str and n
  p=Path(n);assert not p.is_absolute() and '..' not in p.parts and p.as_posix()==n
  p=root/p;assert p.resolve().is_relative_to(root) and not p.is_symlink();return p
 def sha(n):return hashlib.sha256(safe(n).read_bytes()).hexdigest()
 def read(n):return json.loads(safe(n).read_bytes())
 for n,h in [(BASELINE,BASELINE_SHA),(MANIFEST,MANIFEST_SHA),(AUDIT,AUDIT_SHA)]:assert sha(n)==h
 baseline,manifest,audit=read(BASELINE),read(MANIFEST),read(AUDIT)
 assert baseline['status'].endswith('requires_fresh_aggregate_audit')
 assert manifest['status']=='formal_verification_passed_partial_coverage'
 assert manifest['selection']==BASELINE and manifest['selection_sha256']==BASELINE_SHA
 assert manifest['proof_files']==baseline['proof_files'] and len(baseline['proof_files'])==1186
 assert len(manifest['frozen_inputs_sha256'])==50797
 assert audit['status']=='passed' and audit['proof_file_count']==1186 and audit['theorem_count']==9896
 for record in audit['checks']:
  codes=[record[k] for k in ('exit_code','actual_exit_code','actual_runner_exit_code') if k in record]
  assert codes and all(type(c) is int and c==0 for c in codes)
  commands=[record[k] for k in ('command','actual_command') if k in record]
  assert commands and all(type(c) is list and c==commands[0] for c in commands)
  locations=[record[k] for k in ('actual_workdir','working_directory','workdir','cwd') if k in record]
  assert all(type(n) is str and n==locations[0] for n in locations)
  assert 'status' not in record or record['status']=='passed'
 assert audit['proof_sha256']=={n:r['sha256'] for n,r in baseline['proof_files'].items()}
 assert set(baseline['proof_files'])<=set(selected)
 for n,old in baseline['proof_files'].items():
  current=selected[n]
  assert current['sha256']==old['sha256']==sha(n)
  replacements={p:r for p,r in HISTORICAL_EVIDENCE_ALIASES.items() if p in old['evidence_sha256']}
  assert current.get('checkpoint29_historical_evidence_path_replacements',{})==replacements
  if replacements:
   assert current['checkpoint29_original_baseline_evidence']==old
   for p,r in replacements.items():
    assert old['evidence_sha256'][p]==r['sha256']==sha(r['file']) and p not in current['evidence_sha256']
  for key,value in old.items():
   if key=='evidence_sha256':
    assert all(current[key].get(replacements[p]['file'] if p in replacements else p)==h for p,h in value.items())
   else:assert current[key]==value,(n,key)
 extra_replacements={p:r for p,r in HISTORICAL_EVIDENCE_ALIASES.items() if p in baseline['extra_frozen_inputs']}
 assert set(extra_replacements)=={'book/coverage/material-corrections.json'}
 for n,row in baseline['extra_frozen_inputs'].items():
  if n in extra_replacements:
   alias=extra_replacements[n]
   assert row['sha256']==alias['sha256']==sha(alias['file']) and n not in extras
   assert extras.get(alias['file'])==row
  else:assert extras.get(n)==row
 bound={}
 def bind(n,h):
  assert type(h) is str and re.fullmatch('[0-9a-f]{64}',h)
  assert n not in bound or bound[n]==h
  if n not in bound:assert safe(n).is_file() and sha(n)==h
  bound[n]=h
 for n,row in selected.items():
  bind(n,row['sha256'])
  for p,h in row['evidence_sha256'].items():bind(p,h)
 for n,row in extras.items():bind(n,row['sha256'])
 by_digest={}
 for n,h in sorted(bound.items()):by_digest.setdefault(h,n)
 snapshot=manifest['snapshot'];assert safe(snapshot).is_dir() and safe(snapshot).resolve().is_relative_to(root/'reports/full-coverage')
 first=selected[sorted(selected)[0]];rows=[];added={};reused=0
 for n,h in sorted(manifest['frozen_inputs_sha256'].items()):
  safe(n);frozen=snapshot+'/'+n
  assert safe(frozen).resolve().is_relative_to(safe(snapshot).resolve()) and sha(frozen)==h
  retained=by_digest.get(h)
  if retained is None:
   retained=frozen;bind(retained,h);by_digest[h]=retained
   first['evidence_sha256'][retained]=h;added[retained]=h
  else:reused+=1
  assert bound[retained]==h
  rows.append({'original_frozen_path':n,'sha256':h,'retained_input':retained})
 assert len(rows)==50797 and {r['original_frozen_path']:r['sha256'] for r in rows}==manifest['frozen_inputs_sha256']
 for n in [BASELINE,MANIFEST,AUDIT]:bind(n,sha(n));first['evidence_sha256'][n]=sha(n)
 result={'status':'all_original_frozen28_inputs_retained_by_exact_content_fingerprints',
  'prepared_at_utc':datetime.now(timezone.utc).isoformat(),
  'baseline_selection':BASELINE,'baseline_selection_sha256':BASELINE_SHA,
  'baseline_manifest':MANIFEST,'baseline_manifest_sha256':MANIFEST_SHA,
  'baseline_actual_audit':{'file':AUDIT,'sha256':AUDIT_SHA},
  'original_snapshot':snapshot,'original_input_count':len(rows),
  'retained_existing_content_rows':reused,'new_unique_snapshot_aliases':added,
  'new_unique_snapshot_alias_count':len(added),
  'new_unique_snapshot_alias_bytes':sum(safe(n).stat().st_size for n in added),
  'input_bindings':rows,'historical_evidence_path_replacements':{n:r['checkpoint29_historical_evidence_path_replacements'] for n,r in selected.items() if r.get('checkpoint29_historical_evidence_path_replacements')},
  'historical_extra_frozen_input_path_replacements':extra_replacements,
  'original_replaced_extra_frozen_input_rows':{p:baseline['extra_frozen_inputs'][p] for p in extra_replacements},
  'original_row_retrieval':'Immutable original selection/source key retains every original field, semantic body, native execution, raw log and timestamp.',
  'scope':'All1186 selected28 source bytes and all50797 frozen original path/hash bindings retained. Three old Source60 evidence retrieval keys use exact immutable byte aliases, with the entire original row preserved separately. Historical verification remains historical; the new selection requires fresh aggregate verification.'}
 payload=(json.dumps(result,ensure_ascii=False,separators=(',',':'))+'\n').encode()
 assert len(payload)<100_000_000
 destination=safe(destination_name);assert not destination.exists()
 digest=hashlib.sha256(payload).hexdigest()
 first['evidence_sha256'][destination_name]=digest
 return {'provenance':{'file':destination_name,'sha256':digest,'original_inputs':len(rows),'new_snapshot_aliases':len(added)},'payload':payload}
