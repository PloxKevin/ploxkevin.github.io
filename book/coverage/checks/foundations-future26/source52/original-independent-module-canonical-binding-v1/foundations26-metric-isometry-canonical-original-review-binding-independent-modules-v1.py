from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def check(ref):assert H(path(ref['file']))==ref['sha256'];return path(ref['file'])
def ref(n):return {'file':n,'sha256':H(path(n))}
N='book/coverage/checks/foundations-future26/metric-isometry/two-source15-canonical-paired-readiness-v1.json';assert H(R/N)=='047f99bf8bbac7974db392993e316e97531237107bb4553e2b168bd1fefdc950'
r=json.loads((R/N).read_text());assert r['public_theorem_count']==15 and r['actual_canonical_execution_count']==4 and not r['coverage_complete']
p=json.loads(check(r['canonical_preparation']).read_text());iv=json.loads((R/'book/coverage/inventory.json').read_text());um={u['key']:u for u in iv['material_source_units']}
assert H(R/'book/coverage/inventory.json')=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
alias=p['canonical_original_byte_aliases']
for original,a in alias.items():assert check(a).read_bytes()==path(original).read_bytes()
protected=p['protected_current_inputs_sha256']
for n,h in protected.items():assert H(path(n))==h,n
sel=json.loads((R/'reports/full-coverage/checkpoint-25-selection.json').read_text());assert len(sel['proof_files'])==1156
for n,row in sel['proof_files'].items():assert H(R/n)==row['sha256']
groups=[]
for x in r['proof_sources']:
 source=check(x['source']);orig=check(x['original_source']);snapshot=check(x['source_snapshot']);peer=json.loads(check(x['original_semantic_peer']).read_text())
 assert source.read_bytes()==orig.read_bytes()==snapshot.read_bytes() and source.read_text()==peer['full_source_body_read']
 assert peer==x['entire_original_semantic_body_and_time'] and peer['errors']==[] and peer['missing_clauses']==[]
 names=[d['name'] for d in declarations(source.read_text()) if d['kind']in['theorem','lemma']];assert names==x['public_theorems']
 assert peer['whole_literal_keys']==x['whole_literal_keys']
 for u in peer['literal_unit_decisions']:assert u['entire_inventory_record']==um[u['key']] and u['missing_clauses']==[]
 pairs=[]
 for i,a in enumerate(x['actual_canonical_pair']):
  record_path=check(a['record']);d=json.loads(record_path.read_text());codes=[d[k] for k in ['actual_exit_code','exit_code'] if k in d];assert codes and all(type(v)is int and v==0 for v in codes)
  assert d['source']==x['source']['file'] and d['source_sha256_before']==d['source_sha256_after']==x['source']['sha256'] and d['source_unchanged']is True
  commands=[d[k] for k in ['command','actual_command'] if k in d];expected=['lake','env','lean',x['source']['file'].removeprefix('verification/lean/')] if i==0 else ['lake','build','SafeLearning.'+source.stem];assert commands and all(c==expected for c in commands)
  logs=[d[k] for k in ['log','raw_log'] if k in d];hs=[d[k] for k in ['log_sha256','raw_log_sha256'] if k in d];assert logs and hs and all(n==logs[0] for n in logs) and all(h==hs[0] for h in hs) and H(path(logs[0]))==hs[0]
  assert d['protection_errors']==[] and d['started_at_utc']<d['finished_at_utc']
  pairs.append({'record':a['record'],'entire_original_actual_body_and_time':d,'raw_log':ref(logs[0]),'source_snapshot':x['source_snapshot']})
 groups.append({'source':x['source'],'original_semantic_peer':x['original_semantic_peer'],'entire_original_semantic_body_and_time':peer,'literal_unit_decisions_unchanged':peer['literal_unit_decisions'],'public_theorems':names,'actual_canonical_pairs':pairs})
assert sum(len(g['public_theorems'])for g in groups)==15
out=Path('/tmp/foundations26-metric-isometry-canonical-original-body-binding-independent-modules-v1.json');assert not out.exists();body={'status':'passed_independent_narrow_canonical_exact_source_body_and_pair_binding','errors':[],'checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume','canonical_readiness':ref(N),'canonical_preparation':r['canonical_preparation'],'source_count':2,'public_theorem_count':15,'actual_canonical_record_count':4,'original_review_bodies_and_times_preserved':True,'groups':groups,'canonical_original_byte_aliases':alias,'all1156_selected_sources_exact':True,'all31_current52_assets_and_five25_owners_exact':True,'scope':'Narrow source/name/body/original-history/current-literal/actual-pair confirmation only. Original semantic decisions and dates retained unchanged; no semantic redecision, compiler rerun, live candidate installation, aggregate or publication claim.'};out.write_text(json.dumps(body,indent=2)+'\n');print(ref(str(out)))
