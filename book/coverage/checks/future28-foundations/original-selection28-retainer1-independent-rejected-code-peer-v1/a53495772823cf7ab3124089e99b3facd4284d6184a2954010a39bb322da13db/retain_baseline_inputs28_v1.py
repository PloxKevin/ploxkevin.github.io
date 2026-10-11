"""Retain every frozen27 byte and every original selection row without retiming."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,re

BASELINE='reports/full-coverage/checkpoint-27-selection.json'
BASELINE_SHA='ff2cf797d5171fbd9d7edb94683e779cdb442e476dde6f2ccc76470d81186bcd'
MANIFEST='reports/full-coverage/checkpoint-27-manifest.json'
MANIFEST_SHA='196700f9fd69a0a7610f4a2b3d6bad20cfcb34688faa53f5f2fb8b688c085044'
AUDIT='reports/full-coverage/lean-checkpoint-27/verification-original.json'
AUDIT_SHA='fdd431eea1137c48032d20cdb31270b8d76a4ca715f19715167a1ec67cff194f'

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
 assert manifest['proof_files']==baseline['proof_files'] and len(baseline['proof_files'])==1175
 assert len(manifest['frozen_inputs_sha256'])==48662
 assert audit['status']=='passed' and audit['proof_file_count']==1175 and audit['theorem_count']==9644
 assert all(type(r['exit_code']) is int and r['exit_code']==0 for r in audit['checks'])
 assert audit['proof_sha256']=={n:r['sha256'] for n,r in baseline['proof_files'].items()}
 assert set(baseline['proof_files'])<=set(selected)
 for n,old in baseline['proof_files'].items():
  current=selected[n]
  assert current['sha256']==old['sha256']==sha(n)
  for key,value in old.items():
   if key=='evidence_sha256':assert all(current[key].get(p)==h for p,h in value.items())
   else:assert current[key]==value,(n,key)
 for n,row in baseline['extra_frozen_inputs'].items():assert extras.get(n)==row
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
 assert len(rows)==48662 and {r['original_frozen_path']:r['sha256'] for r in rows}==manifest['frozen_inputs_sha256']
 for n in [BASELINE,MANIFEST,AUDIT]:bind(n,sha(n));first['evidence_sha256'][n]=sha(n)
 result={'status':'all_original_frozen27_inputs_retained_by_exact_content_fingerprints',
  'prepared_at_utc':datetime.now(timezone.utc).isoformat(),
  'baseline_selection':BASELINE,'baseline_selection_sha256':BASELINE_SHA,
  'baseline_manifest':MANIFEST,'baseline_manifest_sha256':MANIFEST_SHA,
  'baseline_actual_audit':{'file':AUDIT,'sha256':AUDIT_SHA},
  'original_snapshot':snapshot,'original_input_count':len(rows),
  'retained_existing_content_rows':reused,'new_unique_snapshot_aliases':added,
  'new_unique_snapshot_alias_count':len(added),
  'new_unique_snapshot_alias_bytes':sum(safe(n).stat().st_size for n in added),
  'input_bindings':rows,'historical_evidence_path_replacements':{},
  'original_row_retrieval':'Immutable original selection/source key retains every original field, semantic body, native execution, raw log and timestamp.',
  'scope':'All1175 selected27 source bytes and all48662 frozen original path/hash bindings retained. Historical verification remains historical; the new selection requires fresh aggregate verification.'}
 payload=(json.dumps(result,ensure_ascii=False,separators=(',',':'))+'\n').encode()
 assert len(payload)<100_000_000
 destination=safe(destination_name);assert not destination.exists();destination.parent.mkdir(parents=True,exist_ok=True)
 with destination.open('xb') as f:f.write(payload)
 first['evidence_sha256'][destination_name]=sha(destination_name)
 return {'file':destination_name,'sha256':sha(destination_name),'original_inputs':len(rows),'new_snapshot_aliases':len(added)}
