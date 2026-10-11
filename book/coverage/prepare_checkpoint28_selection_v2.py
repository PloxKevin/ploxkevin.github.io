"""Select eleven exact reviewed additions while retaining all selected27 bytes."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,copy,hashlib,json,re
from lean_names import declarations
from retain_baseline_inputs28_v2 import retain,BASELINE,BASELINE_SHA,MANIFEST,MANIFEST_SHA,AUDIT,AUDIT_SHA

ROOT=Path(__file__).resolve().parents[2]
INVENTORY='book/coverage/inventory-after-correction60.json'
INVENTORY_SHA='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
DESTINATION='reports/full-coverage/checkpoint-28-selection.json'
CONTENT_MAP='book/coverage/checks/frozen27-input-content-bindings28-v1.json'

def safe(n):
 assert type(n) is str and n
 p=Path(n);assert not p.is_absolute() and '..' not in p.parts and p.as_posix()==n
 p=ROOT/p;assert p.resolve().is_relative_to(ROOT) and not p.is_symlink();return p
def sha(n):return hashlib.sha256(safe(n).read_bytes()).hexdigest()
def read(n):return json.loads(safe(n).read_bytes())
def checked(r):
 assert set(r)=={'file','sha256'} and re.fullmatch('[0-9a-f]{64}',r['sha256'])
 assert sha(r['file'])==r['sha256'];return read(r['file'])
def zero(d):
 codes=[d[k] for k in ('actual_exit_code','exit_code','actual_runner_exit_code') if k in d]
 assert codes and all(type(c) is int and c==0 for c in codes)
def native_record(record,expected_command,expected_workdir):
 zero(record)
 commands=[record[k] for k in ('actual_command','command') if k in record]
 assert commands and all(type(c) is list and c==expected_command for c in commands)
 locations=[record[k] for k in ('actual_workdir','workdir','cwd') if k in record]
 assert locations and all(type(n) is str and n==expected_workdir for n in locations)
 assert 'status' not in record or record['status']=='passed'
def exact(mapping):
 for n,h in mapping.items():assert sha(n)==h,n
def merge(target,values):
 for n,h in values.items():
  assert n not in target or target[n]==h
  target[n]=h

def prepare(plan_name,plan_sha256,apply):
 plan=checked({'file':plan_name,'sha256':plan_sha256})
 assert plan['status']=='exact_current60_owner28_and_eleven_sources_explicit_selection_plan'
 peer=checked(plan['independent_selection_helper_review'])
 assert peer['status']==plan['expected_independent_selection_helper_review_status'] and peer['errors']==[]
 helper={'file':Path(__file__).relative_to(ROOT).as_posix(),'sha256':sha(Path(__file__).relative_to(ROOT).as_posix())}
 assert peer['helper']==helper
 dependencies={helper['file']:helper['sha256'],
  'book/coverage/retain_baseline_inputs28_v2.py':'a4f2db8e19b0c35340a65188711bb7fbfaab50fc5109eb08513740621d32ca45',
  'book/coverage/lean_names.py':'9e00c114c57a2bb05939a21bee09679188aa97c855a8d10e61b160f31e10f07d'}
 assert plan['helpers_sha256']==peer['reviewed_helpers_sha256']==dependencies
 exact(dependencies)
 assert plan['baseline_selection']=={'file':BASELINE,'sha256':BASELINE_SHA}
 assert plan['baseline_manifest']=={'file':MANIFEST,'sha256':MANIFEST_SHA}
 assert plan['baseline_audit']=={'file':AUDIT,'sha256':AUDIT_SHA}
 baseline,manifest,audit=[checked(plan[k]) for k in ['baseline_selection','baseline_manifest','baseline_audit']]
 assert len(baseline['proof_files'])==1175 and audit['proof_file_count']==1175 and audit['theorem_count']==9644
 assert audit['status']=='passed'
 for record in audit['checks']:
  zero(record)
  commands=[record[k] for k in ('actual_command','command') if k in record]
  assert commands and all(type(c) is list and c==commands[0] for c in commands)
  locations=[record[k] for k in ('actual_workdir','workdir','cwd') if k in record]
  assert all(type(n) is str and n==locations[0] for n in locations)
  assert 'status' not in record or record['status']=='passed'
 assert audit['proof_sha256']=={n:r['sha256'] for n,r in baseline['proof_files'].items()}
 assert manifest['proof_files']==baseline['proof_files'] and len(manifest['frozen_inputs_sha256'])==48662
 assert plan['inventory']=={'file':INVENTORY,'sha256':INVENTORY_SHA} and sha('book/coverage/inventory.json')==INVENTORY_SHA
 checked(plan['inventory'])
 integration=checked(plan['integration_result']);execution=checked(plan['actual_integration_execution']);zero(execution)
 assert integration['status']=='four_exact_reviewed_owner28_candidate_bytes_integrated_pending_fresh_current60_global_integrity_and_aggregate28_audit'
 assert integration['applied'] is True and integration['inventory_sha256']==INVENTORY_SHA
 binding_ref={'file':integration['binding_manifest'],'sha256':integration['binding_manifest_sha256']};binding=checked(binding_ref)
 helper_ref=integration['actual_helper'];assert binding['helper']==helper_ref
 native_record(execution,['python3',helper_ref['file'],'--binding',binding_ref['file'],'--binding-sha256',binding_ref['sha256'],'--apply'],str(ROOT))
 assert execution['actual_workdir']==str(ROOT) and execution['helper_sha256_before']==execution['helper_sha256_after']=={helper_ref['file']:helper_ref['sha256']}
 exact(execution['helper_sha256_after']);assert sha(execution['log'])==execution['log_sha256']
 replacements={r['destination']:r for r in integration['exact_replacements']}
 assert len(replacements)==5 and set(replacements)=={'book/coverage/'+n+'.json' for n in ['core','foundations','applied','modules','applied-promotions']}
 for n,row in replacements.items():
  checked(row['candidate']);assert sha(n)==row['candidate']['sha256'] and sha(row['original27_byte_copy'])==row['before_sha256']
 selected=copy.deepcopy(baseline['proof_files']);first=selected[sorted(selected)[0]]
 expected={};pairs=[]
 for batch in binding['canonical_pair_batches']:
  readiness=checked(batch['readiness']);actual=checked(batch['actual_execution']);zero(actual)
  assert readiness['status']==batch['expected_readiness_status'] and readiness['errors']==[]
  assert readiness['source_count']==batch['source_count'] and readiness['public_theorem_count']==batch['public_theorem_count']
  assert readiness['actual_compiler_command_count']==len(readiness['actual_paired_records'])==2*batch['source_count']
  native_record(actual,batch['expected_command'],str(ROOT))
  assert actual['helper_sha256_before']==actual['helper_sha256_after']==batch['expected_helper_sha256']
  exact(actual['helper_sha256_after']);assert sha(actual['log'])==actual['log_sha256']
  for r in readiness['sources']:
   n=r['canonical_source'];assert n not in expected and n not in selected
   expected[n]=r['original_tmp_source']['sha256']
  pairs+=readiness['actual_paired_records']
 assert len(expected)==11 and len(pairs)==22
 seen=set();offers={};peers={}
 for owner,row in binding['owners'].items():
  offer=checked(row['reviewed_offer']);peer=checked(row['final_mapping_peer'])
  assert peer['status']==row['expected_final_mapping_peer_status'] and peer['errors']==[]
  assert row['candidate']==replacements[row['destination']]['candidate'] and offer['candidate']==row['candidate']
  assert offer['inventory_sha256']==INVENTORY_SHA
  exact(offer['source_sha256']);exact(offer['required_evidence_artifacts_sha256'])
  merge(first['evidence_sha256'],offer['required_evidence_artifacts_sha256'])
  for n,proof in offer['proof_files'].items():
   assert n in expected and n not in seen and proof['sha256']==expected[n];seen.add(n)
   exact(proof['evidence_sha256'])
   pair=[p for p in pairs if p['source']['file']==n]
   assert len(pair)==2 and {p['kind'] for p in pair}=={'standalone','named'} and proof['actual_pair']==pair
   for p in pair:
    native=checked(p['actual_record']);zero(native)
    command=['lake','env','lean','SafeLearning/'+Path(n).name] if p['kind']=='standalone' else ['lake','build','SafeLearning.'+Path(n).stem]
    native_record(native,command,str(ROOT/'verification/lean'))
    assert native['source']==n and native['source_sha256_before']==native['source_sha256_after']==expected[n]
    assert p['raw_log']=={'file':native['log'],'sha256':native['log_sha256']}
    for key in ('actual_record','raw_log','source_snapshot'):
     r=p[key];assert sha(r['file'])==r['sha256'] and proof['evidence_sha256'][r['file']]==r['sha256']
   selected[n]=copy.deepcopy(proof)
   selected[n]['original_actual_zero_record']=next(p['actual_record']['file'] for p in pair if p['kind']=='standalone')
  offers[row['reviewed_offer']['file']]=row['reviewed_offer']['sha256'];peers[owner]=row['final_mapping_peer']
  for r in [row['reviewed_offer'],row['final_mapping_peer'],row['actual_finalizer'],row['candidate']]:merge(first['evidence_sha256'],{r['file']:r['sha256']})
 assert seen==set(expected) and len(selected)==1186
 for n,row in selected.items():assert sha(n)==row['sha256']
 all_names=[d['name'] for n in selected for d in declarations(safe(n).read_text())]
 assert len(all_names)==len(set(all_names))
 theorem_names=[d['name'] for n in selected for d in declarations(safe(n).read_text()) if d['kind'] in {'theorem','lemma'}]
 assert len(theorem_names)==len(set(theorem_names))==9896
 new_names=[d['name'] for n in expected for d in declarations(safe(n).read_text()) if d['kind'] in {'theorem','lemma'}]
 assert len(new_names)==len(set(new_names))==252
 for owner in binding['owners']:
  ledger=read('book/coverage/'+owner+'.json')
  for c in ledger['material_claims']+[c for e in ledger['exercises'] for c in e['claims']]:assert set(c['lean_declarations'])<=set(all_names)
 for n in selected:
  for line in re.findall(r'^import[^\n]*',safe(n).read_text(),re.M):
   for dep in line.split()[1:]:
    if dep.startswith('SafeLearning.'):assert 'verification/lean/'+dep.replace('.','/')+'.lean' in selected
 global_audit=checked(plan['global_integrity'])
 assert global_audit['integrity_status']=='passed' and global_audit['errors']==[] and global_audit['mathematical_coverage_complete'] is False
 assert global_audit['inventory_sha256']==INVENTORY_SHA
 assert len(global_audit['domains'])==4 and {r['domain'] for r in global_audit['domains']}==set(binding['owners'])
 for r in global_audit['domains']:assert r['ledger_sha256']==replacements['book/coverage/'+r['domain']+'.json']['candidate']['sha256']
 extras=copy.deepcopy(baseline['extra_frozen_inputs'])
 for n,row in plan['additional_frozen_inputs'].items():
  assert set(row)=={'sha256','scope'} and row['scope']=='immutable_audit_or_local_source_evidence'
  assert any(safe(n).resolve().is_relative_to((ROOT/p).resolve()) for p in ['book/coverage','reports/full-coverage/source-history'])
  assert sha(n)==row['sha256'] and (n not in extras or extras[n]==row);extras[n]=row
 for r in [plan['global_integrity'],plan['integration_result'],plan['actual_integration_execution'],binding_ref,plan['independent_selection_helper_review']]:merge(first['evidence_sha256'],{r['file']:r['sha256']})
 merge(first['evidence_sha256'],{plan_name:plan_sha256})
 merge(first['evidence_sha256'],plan['helpers_sha256'])
 exact(first['evidence_sha256'])
 if not apply:return {'status':'passed_selection28_preflight_no_writes','proofs':1186,'new_sources':11,'new_theorems':252}
 assert not safe(DESTINATION).exists() and not safe(CONTENT_MAP).exists()
 retained=retain(ROOT,selected,extras,CONTENT_MAP)
 provenance=retained['provenance']
 result={'status':'explicit_current60_source_matched_selection_requires_fresh_aggregate_audit',
  'created_at_utc':datetime.now(timezone.utc).isoformat(),
  'baseline_selection':BASELINE,'baseline_selection_sha256':BASELINE_SHA,
  'actual_passing_baseline_audit':AUDIT,'actual_passing_baseline_audit_sha256':AUDIT_SHA,
  'current_inventory':INVENTORY,'current_inventory_sha256':INVENTORY_SHA,
  'offers_sha256':offers,'independent_owner_mapping_peers':peers,
  'global_integrity':plan['global_integrity']['file'],'global_integrity_sha256':plan['global_integrity']['sha256'],
  'proof_files':dict(sorted(selected.items())),'proof_file_count':1186,'new_file_count':11,
  'extra_frozen_inputs':extras,'previous_frozen_input_content_binding':provenance,
  'selection_plan':plan_name,'selection_plan_sha256':plan_sha256,'deliberate_baseline_source_revisions':{},
  'coverage_complete':False,
  'limits':['All1175 baseline27 sources and full original selection rows retained. Eleven additions require fresh frozen28 aggregate build, kernel replay and all9896 public theorem/lemma axiom checks.',
            'All48662 original frozen27 path/hash bindings retained. Previous commands, results, bodies, raw logs and times remain historical.',
            'Remaining exercises and material stay pending; no whole-book completion claim.']}
 payload=(json.dumps(result,ensure_ascii=False,separators=(',',':'))+'\n').encode();assert len(payload)<100_000_000
 assert not safe(DESTINATION).exists() and not safe(CONTENT_MAP).exists()
 assert len(retained['payload'])<100_000_000
 for n,row in selected.items():assert sha(n)==row['sha256']
 for n,h in dependencies.items():assert sha(n)==h
 content=safe(CONTENT_MAP);content.parent.mkdir(parents=True,exist_ok=True)
 with content.open('xb') as f:f.write(retained['payload'])
 assert sha(CONTENT_MAP)==provenance['sha256']
 with safe(DESTINATION).open('xb') as f:f.write(payload)
 return {'status':'prepared_selection28_requires_fresh_aggregate','proofs':1186,'new_sources':11,'sha256':sha(DESTINATION),'content_map':provenance}

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--plan',required=True);parser.add_argument('--plan-sha256',required=True);parser.add_argument('--apply',action='store_true');args=parser.parse_args()
 print(json.dumps(prepare(args.plan,args.plan_sha256,args.apply)))
