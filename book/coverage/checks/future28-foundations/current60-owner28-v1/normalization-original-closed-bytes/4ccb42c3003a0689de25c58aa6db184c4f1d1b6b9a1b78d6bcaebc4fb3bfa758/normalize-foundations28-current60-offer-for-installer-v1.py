from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B='book/coverage/checks/future28-foundations/current60-owner28-v1';D=B+'/foundations28-current60-offer-draft-v2.json';OUT=B+'/foundations28-current60-offer-draft-v3.json'
def h(n):return hashlib.sha256((R/n).read_bytes()).hexdigest()
def j(n):return json.loads((R/n).read_bytes())
def ref(n):return {'file':n,'sha256':h(n)}
assert not(R/OUT).exists()and h(D)=='ccb77f068302a1a11732a0c38b787ce5aa4f722c896df438d869c0824976f043'
d=j(D);readiness='book/coverage/checks/future28-core/current60-canonical-pairs-v1/actual-current60-canonical-paired-readiness28-v1.json';ready=j(readiness);pins=ready['protected_inputs_sha256']
def guard():
 for n,s in pins.items():assert h(n)==s,n
 assert h(D)=='ccb77f068302a1a11732a0c38b787ce5aa4f722c896df438d869c0824976f043'and h(d['candidate']['file'])==d['candidate']['sha256']
guard();out=copy.deepcopy(d)
for n,row in out['proof_files'].items():
 pair=[p for p in ready['actual_paired_records']if p['source']['file']==n]
 assert len(pair)==2 and {p['kind']for p in pair}=={'standalone','named'}
 assert pair==[row['actual_pair']['standalone'],row['actual_pair']['named']]
 assert set(row['mapped_named_declarations'])==set(row['public_theorem_names'])
 row['actual_pair']=pair;row['mapped_named_declarations']=copy.deepcopy(row['public_theorem_names'])
mutable={'book/coverage/'+n+'.json'for n in ['core','foundations','applied','modules','applied-promotions']}
closed=copy.deepcopy(out['additional_frozen_inputs'])
def add(n,s):
 assert type(n)is str and n and not Path(n).is_absolute()and '..'not in Path(n).parts and n not in mutable
 assert h(n)==s,n;assert n not in closed or closed[n]==s;closed[n]=s
for r in [out['candidate'],out['exact_interface'],out['integrity'],out['original_installed27_ledger'],out['inventory'],out['actual_canonical_readiness'],out['actual_canonical_outer_execution'],out['actual_candidate_preparation'],out['actual_candidate_preparation_raw_log'],out['candidate_builder'],out['candidate_preparation_runner'],out['original_preparation_draft'],out['preparation_original_byte_catalog'],ref(D)]:add(r['file'],r['sha256'])
def walk(value):
 if isinstance(value,dict):
  if {'file','sha256'}<=set(value) and type(value['file'])is str and not Path(value['file']).is_absolute():add(value['file'],value['sha256'])
  for v in value.values():walk(v)
 elif isinstance(value,list):
  for v in value:walk(v)
cats=[]
for p in (R/'book/coverage/checks/future28-foundations').rglob('*aliases-v1.json'):
 prefix=p.relative_to(R/'book/coverage/checks/future28-foundations').parts[0]
 if prefix.startswith(('original-residual17','original-allocation19','original-literal-gradient15','original-literal-partial7','original-literal-jacobian','original-chain-lie11','original-foundations-current60')):
  n=str(p.relative_to(R));add(n,h(n));walk(j(n));cats.append(ref(n))
assert cats and all(n not in mutable and not Path(n).is_absolute()for n in closed)
for n,s in closed.items():assert h(n)==s,n
out['required_evidence_artifacts_sha256']=closed
out['original_proofmetadata_draft2']=ref(D);out['original_scope_history_byte_catalogs']=cats
out['installer_schema_normalization']={'normalized_at_utc':datetime.now(timezone.utc).isoformat(),'scope':'Only new proof metadata pair shape and native declaration ordering match the actual Root installer contract; candidate and whole literal interface bytes remain unchanged. Complete immutable ROOT-relative evidence map added; five mutable live owner paths excluded.','candidate_or_math_or_source_changed':False,'original_actual_preparation':out['actual_candidate_preparation'],'actual_normalization_record_pending':True}
guard()
with (R/OUT).open('x')as f:json.dump(out,f,indent=2);f.write('\n')
guard()
print(json.dumps({'offer':ref(OUT),'candidate':out['candidate'],'closed_evidence_count':len(closed),'original_catalog_count':len(cats)}))
