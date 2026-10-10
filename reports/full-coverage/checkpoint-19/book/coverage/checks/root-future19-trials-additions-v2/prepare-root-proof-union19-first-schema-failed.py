from pathlib import Path
import json,hashlib,re
R=Path('/home/oxrexkevin/SafetyBased');H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest();L=lambda n:json.loads((R/n).read_text())
base=L('reports/full-coverage/checkpoint-18-selection.json');union={k:dict(v) for k,v in base['proof_files'].items()};origins={k:['checkpoint18'] for k in union}
def merge(n,record,origin):
 assert H(n)==record['sha256'],n
 for p,h in record.get('evidence_sha256',{}).items():assert H(p)==h,p
 if n in union:
  assert union[n]['sha256']==record['sha256'];union[n].setdefault('evidence_sha256',{}).update(record.get('evidence_sha256',{}))
 else:union[n]=record
 origins.setdefault(n,[]).append(origin)
for n,rec in L('book/coverage/foundations-audit19-additions.json')['proof_files'].items():merge(n,rec,'foundation_original33_proof_only')
a=L('book/coverage/applied-audit19-additions.json')
for row in a['modules']:
 n=row['source'];h=row['sha256_after'];assert row['exit_code']==0 and row['sha256_before']==h
 provenance=row['original_execution_provenance'];p=provenance['canonical_byte_identical_original_record'];actual=L(p);assert actual['exit_code']==0
 merge(n,dict(sha256=h,evidence_sha256={p:provenance['canonical_original_record_sha256'],row['log']:row['log_sha256']},evidence_scope='Original actual standalone compiler and exact log bytes; fresh aggregate audit required.'),'applied_original33_proof_only')
for n,rec in L('book/coverage/checks/modules-audit19-additions.json')['proof_files'].items():merge(n,rec,'modules_original33_proof_only')
core=L('book/coverage/core.json')['proof_files'];missing=sorted(set(core)-set(union))
print('Initialexplicitproofunion',len(union),'coreproofsneedrecords',missing)
closure_missing={}
for n in list(union)+missing:
 for dep in re.findall(r'^import\s+(SafeLearning\.\S+)',(R/n).read_text(),re.M):
  name='verification/lean/'+dep.replace('.','/')+'.lean'
  if name not in union and name not in missing:closure_missing[name]=H(name)
print('Additionalforeignimports',closure_missing)
D=R/'book/coverage/checks/root-source44-candidate-proof-union19-v1.json';assert not D.exists();D.write_text(json.dumps(dict(status='read_only_original33_proof_union_source_hashes_and_evidence_checked_not_final_source44_selection',proof_files=union,origins=origins,root_core_sources_needing_actual_records=missing,additional_local_imports_needing_actual_records=closure_missing,limits=['Proof-source identities only; current44 review/ledger/offer bindings must be independently complete before final selection.','No aggregate/kernel/axiom run is inferred from this preparation.']),indent=2)+'\n')
