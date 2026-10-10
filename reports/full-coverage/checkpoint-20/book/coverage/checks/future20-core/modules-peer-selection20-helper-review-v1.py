from pathlib import Path
import ast,json,hashlib,re
from datetime import datetime,timezone
R=Path('/home/oxrexkevin/SafetyBased');H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest();L=lambda n:json.loads((R/n).read_text())
helper='book/coverage/prepare_checkpoint20_selection.py';tree=ast.parse((R/helper).read_text());writes=[]
for n in ast.walk(tree):
 if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in {'write_text','write_bytes','unlink','mkdir','replace','rename'}:writes.append(ast.unparse(n))
assert len(writes)==1 and writes[0].startswith('destination.write_text(')
assert "assert not destination.exists()" in (R/helper).read_text()
assert "explicit_current47_source_matched_selection_requires_fresh_aggregate_audit" in (R/helper).read_text()
assert "coverage_complete=False" in (R/helper).read_text()
baseline=L('reports/full-coverage/checkpoint-19-selection.json');audit=L('reports/full-coverage/lean-checkpoint-19/verification-original.json');manifest=L('reports/full-coverage/checkpoint-19-manifest.json')
assert len(baseline['proof_files'])==1055 and audit['status']=='passed'
assert audit['proof_sha256']=={n:r['sha256'] for n,r in baseline['proof_files'].items()}
# Independently verify every actual new compiler invocation and immutable raw log.
new={};records=[]
for offer in ['book/coverage/checks/modules-audit20-source47-additions-v1.json','book/coverage/core-audit20-source47-additions-v1.json']:
 d=L(offer)
 for s,r in d['proof_files'].items():
  assert s not in baseline['proof_files'];assert H(s)==r['sha256']
  for n,h in r['evidence_sha256'].items():assert H(n)==h
  candidates=[]
  for n in r['evidence_sha256']:
   if not n.endswith('.json'):continue
   q=L(n)
   if not isinstance(q,dict) or q.get('source')!=s or q.get('exit_code')!=0:continue
   cmd=q.get('command',q.get('actual_command'))
   if cmd!=['lake','env','lean',str(Path(s).relative_to('verification/lean'))]:continue
   assert q['source_unchanged'] is True and q['source_sha256_before']==q['source_sha256_after']==r['sha256']
   assert Path(q['actual_workdir']).resolve()==(R/'verification/lean').resolve()
   logs=[p for p,h in r['evidence_sha256'].items() if p.endswith('.log') and h==q['log_sha256']];assert logs
   candidates.append((n,logs))
  assert candidates
  records.append({'source':s,'source_sha256':r['sha256'],'actual_standalone_record':candidates[0][0],'raw_log_paths':candidates[0][1]});new[s]=r
assert len(new)==13
selected=set(baseline['proof_files'])|set(new);assert len(selected)==1068
for s in new:
 for line in re.findall(r'^import[^\n]*',(R/s).read_text(),re.M):
  for dep in line.split()[1:]:
   if dep.startswith('SafeLearning.'):assert 'verification/lean/'+dep.replace('.','/')+'.lean' in selected
imports=L('book/coverage/checks/modules-audit20-source47-additions-v1.json')['required_external_import_dependencies'];assert len(imports)==58 and set(imports)<=set(baseline['proof_files'])
for n,h in imports.items():assert H(n)==h==baseline['proof_files'][n]['sha256']
assert len(manifest['frozen_inputs_sha256'])==14101
for n,h in manifest['frozen_inputs_sha256'].items():assert H(manifest['snapshot']+'/'+n)==h
for n,r in baseline['proof_files'].items():
 assert H(n)==r['sha256']
 for p,h in r['evidence_sha256'].items():assert H(p)==h
out=Path('/tmp/modules-checkpoint20-selection-helper-independent-review-v1.json');assert not out.exists();out.write_text(json.dumps({'status':'independent_selection_helper_and_thirteen_actual_additions_guard_review_passed','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':helper,'helper_sha256':H(helper),'actual_readonly_peer_execution_exit_code':0,'baseline_proof_count':1055,'prospective_selected_proof_count':1068,'new_proof_count':13,'exact_new_actual_standalone_records':records,'module58imports_already_selected19':True,'frozen19_inputs_rehashed':14101,'baseline_source_and_original_evidence_hashes_rehashed':True,'write_scope':writes,'guard_findings':['Exact source hash before/after, explicit unchanged flag, exact standalone command, real working directory and raw-log fingerprint checked.','All four current47 owner offers and the fresh global validator must match at actual selection preparation; missing/stale inputs fail before selection write.','The selected set is prospective: no fresh checkpoint20 aggregate, kernel or axiom success is claimed.','All14101 frozen19 inputs and actual original audit outputs remain historical evidence; they are not labeled new executions.','Typed required attribution artifacts are distinct from external full-paper references; baseline located-text/harness aliases retained.'],'limits':['This report reviews the preparation helper and actual thirteen new source records before owner execution. It does not claim that a checkpoint20 selection or frozen checkpoint was created.','Root owns selection preparation and future aggregate verification.']},indent=2)+'\n');print(out,H(str(out)))
