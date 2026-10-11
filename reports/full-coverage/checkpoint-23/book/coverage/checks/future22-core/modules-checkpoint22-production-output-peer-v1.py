from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
cache={}
def safe(n):
 p=Path(n);assert isinstance(n,str) and n and not p.is_absolute() and '..' not in p.parts and str(p)==n and (R/p).resolve().is_relative_to(R.resolve()),n;return R/p
def H(n):
 p=Path(n);p=p if p.is_absolute() else safe(n);st=p.stat();k=(str(p.resolve()),st.st_size,st.st_mtime_ns)
 if k not in cache:cache[k]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[k]
def L(n):return json.loads(safe(n).read_text())
def checked(r):assert set(r)=={'file','sha256'} and H(r['file'])==r['sha256'];return L(r['file'])
def zero(r):
 codes=[r[k] for k in ('actual_exit_code','exit_code') if k in r];assert codes and all(type(c)is int and c==0 for c in codes)
S='reports/full-coverage/checkpoint-22-selection.json';s=L(S);sn=H(S);assert s['proof_file_count']==len(s['proof_files'])==1113 and s['new_file_count']==24 and s['coverage_complete'] is False
assert s['status']=='explicit_current48_source_matched_selection_requires_fresh_aggregate_audit' and s['deliberate_baseline_source_revisions']=={}
PLAN='book/coverage/checks/future22-core/checkpoint22-installed-owner-selection-plan-v1.json';plan=L(PLAN);assert H(PLAN)==s['selection_plan_sha256']=='07e5cfdda3a8b48c1235af394a3d139ad10267ad51acbee4ef7545baa27f84f9' and s['selection_plan']==PLAN
pp='book/coverage/checks/future22-core/checkpoint22-installed-owner-selection-plan-independent-applied-confirmation-v1.json';peer=L(pp);assert H(pp)=='88c6cad37d02e6594d33675edc710222a2e1df011f2cd897826a4aaaf479f0dd' and 'passed' in peer['status'] and not peer['errors'] and peer['selection_plan']=={'file':PLAN,'sha256':H(PLAN)}
HELP='book/coverage/prepare_checkpoint22_selection.py';assert H(HELP)==plan['helpers_sha256'][HELP]=='a4e8cde9db0428bbda076a139208a0e12ac35af4922b9e377b0ca709e25849f6'
RETAINER='book/coverage/retain_baseline_inputs22.py';assert H(RETAINER)==plan['helpers_sha256'][RETAINER]=='a6d122cfc0000360185acf9628693d4e041eefe0ed8b96e0f0bff5fb047859d1'
en='reports/full-coverage/prepare-checkpoint22-selection-execution-v1.json';e=L(en);zero(e)
command=e.get('command',e.get('actual_command'));assert command in [['python3',HELP,'--plan',PLAN],['python',HELP,'--plan',PLAN]] and Path(e['actual_workdir']).resolve()==R
before=e['helper_sha256_before'];after=e['helper_sha256_after'];assert before==after
if isinstance(after,dict):
 assert after[HELP]==H(HELP)
 for n,h in after.items():assert H(n)==h
else:assert after==H(HELP)
assert H(e['log'])==e['log_sha256']
if 'selection_sha256' in e:assert e['selection_sha256']==sn
base=checked(plan['baseline_selection']);audit=checked(plan['baseline_audit']);manifest=checked(plan['baseline_manifest']);assert len(base['proof_files'])==1089 and audit['status']=='passed' and audit['proof_file_count']==1089 and all(c['exit_code']==0 for c in audit['checks'])
assert audit['proof_sha256']=={n:r['sha256'] for n,r in base['proof_files'].items()}
assert s['baseline_selection']==plan['baseline_selection']['file'] and s['baseline_selection_sha256']==plan['baseline_selection']['sha256']
new=set(s['proof_files'])-set(base['proof_files']);assert len(new)==24 and new==set(plan['expected_new_proof_sources'])
firstsource=sorted(base['proof_files'])[0]
for source,row in base['proof_files'].items():
 now=s['proof_files'][source]
 for k,v in row.items():
  if k=='evidence_sha256':assert all(now[k].get(n)==h for n,h in v.items()),source
  else:assert now[k]==v,(source,k)
 allowed={'checkpoint22_inherited_snapshot_provenance_scope'} if source==firstsource else set()
 assert set(now)-set(row)<=allowed and H(source)==row['sha256']
 for n,h in row['evidence_sha256'].items():assert H(n)==h
for n,row in base['extra_frozen_inputs'].items():assert s['extra_frozen_inputs'][n]==row
allnamed={};offered={};ownerpairs={};selectedrefs={}
for owner,refs in plan['owners'].items():
 offer=checked(refs['offer']);ledger=checked(refs['ledger']);assert s['offers_sha256'][refs['offer']['file']]==refs['offer']['sha256']
 assert offer.get('mapped_ledger',offer.get('module_ledger'))==refs['ledger']['file']=='book/coverage/'+owner+'.json'
 assert offer.get('mapped_ledger_sha256',offer.get('module_ledger_sha256'))==refs['ledger']['sha256']
 assert set(offer['proof_files'])==set(refs['expected_owned_proof_sources'])
 for ref in refs.values():
  if isinstance(ref,dict) and set(ref)=={'file','sha256'}:assert H(ref['file'])==ref['sha256'];selectedrefs[ref['file']]=ref['sha256']
 for n,h in offer['required_live_integration_evidence_sha256'].items():assert H(n)==h;selectedrefs[n]=h
 opairs={}
 for source,row in offer['proof_files'].items():
  assert source in new and source not in offered;offered[source]=row;now=s['proof_files'][source]
  assert H(source)==row['sha256']
  for k,v in row.items():assert now[k]==v,(source,k)
  pairs={'standalone':[],'named':[]}
  for n,h in row['evidence_sha256'].items():
   assert H(n)==h
   if not n.endswith('.json'):continue
   a=L(n)
   if not isinstance(a,dict):continue
   cmd=a.get('command',a.get('actual_command'))
   if not isinstance(cmd,list):continue
   kind='standalone' if len(cmd)==4 and cmd[:3]==['lake','env','lean'] else 'named' if cmd==['lake','build','SafeLearning.'+Path(source).stem] or len(cmd)==6 and cmd[:4]==['lake','env','lean','-o'] else None
   if not kind:continue
   recsource=a.get('source',a.get('lean_file'))
   if recsource not in {source,cmd[-1]} or a.get('source_sha256_before')!=row['sha256'] or a.get('source_sha256_after')!=row['sha256']:continue
   zero(a);assert a.get('source_unchanged',True) is True
   assert Path(a.get('actual_workdir',a.get('actual_cwd',a.get('cwd')))).resolve()==R/'verification/lean'
   logh=a.get('log_sha256',a.get('raw_log_sha256'));assert any(q.endswith('.log') and hh==logh for q,hh in row['evidence_sha256'].items())
   canonical=str(Path(source).relative_to('verification/lean'))
   if kind=='standalone' and cmd[-1]!=canonical:
    assert Path(cmd[-1]).is_absolute() and a.get('source_snapshot_sha256',a.get('preserved_source_sha256'))==row['sha256'] and row['sha256'] in row['evidence_sha256'].values()
   snapshot=a.get('source_snapshot_sha256',a.get('preserved_source_sha256'))
   if snapshot is not None:assert snapshot==row['sha256'] and snapshot in row['evidence_sha256'].values()
   pairs[kind].append({'file':n,'sha256':h})
  assert pairs['standalone'] and pairs['named'],source
  assert now['original_actual_zero_record'] in [p['file'] for p in pairs['standalone']]
  opairs[source]=pairs
 ownerpairs[owner]=opairs
assert set(offered)==new
bound={};decls={}
for n,row in s['proof_files'].items():
 assert H(n)==row['sha256'];bound[n]=row['sha256'];decls[n]=declarations(safe(n).read_text())
 for q,h in row['evidence_sha256'].items():assert H(q)==h and (q not in bound or bound[q]==h);bound[q]=h
 for line in re.findall(r'^import[^\n]*',safe(n).read_text(),re.M):
  for dep in line.split()[1:]:
   if dep.startswith('SafeLearning.'):assert 'verification/lean/'+dep.replace('.','/')+'.lean' in s['proof_files'],(n,dep)
for n,row in s['extra_frozen_inputs'].items():assert H(n)==row['sha256'] and (n not in bound or bound[n]==row['sha256']);bound[n]=row['sha256']
for n,h in selectedrefs.items():assert bound[n]==h,(n,'missing actual integration/history/peer binding')
pr=s['previous_frozen_input_content_binding'];pn=pr['file'];assert H(pn)==pr['sha256'];pm=L(pn)
assert pm['status']=='all_original_frozen_inputs_retained_by_exact_content_fingerprints' and pm['baseline_manifest']==plan['baseline_manifest']['file'] and pm['baseline_manifest_sha256']==plan['baseline_manifest']['sha256']
assert pm['baseline_selection']==s['baseline_selection'] and pm['baseline_selection_sha256']==s['baseline_selection_sha256']
assert len(manifest['frozen_inputs_sha256'])==pm['original_input_count']==pr['original_inputs']==32040
rows=pm['input_bindings'];assert len(rows)==32040 and {r['original_frozen_path']:r['sha256'] for r in rows}==manifest['frozen_inputs_sha256'];seen={}
for r in rows:
 name=r['original_frozen_path'];safe(name);target=r['retained_input'];safe(target);h=r['sha256']
 assert H(str(Path(manifest['snapshot'])/name))==H(target)==h==bound[target]
 assert h not in seen or seen[h]==target;seen[h]=target
aliases=pm['new_unique_snapshot_aliases'];assert len(aliases)==pm['new_unique_snapshot_alias_count']==pr['new_snapshot_aliases']
assert pm['retained_existing_content_rows']+len(aliases)==32040 and sum(safe(n).stat().st_size for n in aliases)==pm['new_unique_snapshot_alias_bytes'] and len(set(aliases.values()))==len(aliases)
first=s['proof_files'][firstsource]
for n,h in aliases.items():assert n.startswith(manifest['snapshot']+'/') and H(n)==h==first['evidence_sha256'][n]
initialbound={n:h for n,h in bound.items() if n not in aliases and n!=pn};assert not set(aliases.values())&set(initialbound.values())
assert not set(plan['excluded_full_external_reference_sha256'])&{r['sha256'] for r in s['extra_frozen_inputs'].values()}
dep=L('book/coverage/checks/modules-source44-canonical-dependency-manifest19-v1.json');required=[r for r in dep['artifacts'] if r['required_for_execution_or_immutable_provenance_freeze'] and Path(r['path']).suffix in ['.txt','.cjs']];assert len(required)==49
for r in required:assert s['extra_frozen_inputs'][r['path']]['sha256']==H(r['path'])==r['sha256']
g=checked(plan['global_integrity']);assert g['integrity_status']=='passed' and g['errors']==[] and g['inventory_sha256']==s['current_inventory_sha256']==H(s['current_inventory'])==H('book/coverage/inventory.json')
names={d['name'] for ds in decls.values() for d in ds};theorems=[d for ds in decls.values() for d in ds if d['kind'] in {'theorem','lemma'}]
for domain in g['domains']:
 name='book/coverage/'+domain['domain']+'.json';assert H(name)==domain['ledger_sha256'];ledger=L(name)
 for c in ledger['material_claims']+[c for ex in ledger['exercises'] for c in ex['claims']]:assert set(c['lean_declarations'])<=names,(name,c['id'])
for owner,refs in plan['owners'].items():
 deps=checked(refs['offer']).get('required_external_import_dependencies',{})
 for n,h in deps.items():assert n in s['proof_files'] and H(n)==h
assert H(S)==sn and H(HELP)==plan['helpers_sha256'][HELP]
out='/tmp/modules-checkpoint22-production-output-independent-confirmation-v1.json'
report={'status':'independent_actual_checkpoint22_selection_and_retained_content_confirmation_passed','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'selection':S,'selection_sha256':sn,'actual_production_execution':en,'actual_production_execution_sha256':H(en),'actual_production_raw_log':e['log'],'actual_production_raw_log_sha256':H(e['log']),'selection_plan':{'file':PLAN,'sha256':H(PLAN)},'independent_final_plan_peer':{'file':pp,'sha256':H(pp)},'selection_helper':HELP,'selection_helper_sha256':H(HELP),'baseline_content_binding':pn,'baseline_content_binding_sha256':H(pn),'offers_sha256':s['offers_sha256'],'current_inventory':s['current_inventory'],'current_inventory_sha256':s['current_inventory_sha256'],'global_integrity':plan['global_integrity'],'counts':{'baseline_sources':1089,'new_actual_paired_sources':24,'selected_sources':1113,'public_theorem_or_lemma_exports':len(theorems),'all_typed_declaration_names':len(names),'original_frozen21_input_paths_and_bytes':32040,'distinct_original_frozen_byte_hashes':len(seen),'new_unique_snapshot_aliases':len(aliases),'new_unique_snapshot_alias_bytes':pm['new_unique_snapshot_alias_bytes'],'retained_existing_content_rows':pm['retained_existing_content_rows'],'required_located_primary_text_and_executed_cjs':49,'extra_frozen_inputs':len(s['extra_frozen_inputs'])},'new_source_original_paired_records':ownerpairs,'all5_original21_ledger_bytes_and_actual_copy_execution_explicitly_retained':True,'all_baseline_source_evidence_body_commands_and_times_unchanged':True,'all32040_original_paths_resolve_to_exact_retained_input_bytes':True,'all_added_snapshot_aliases_necessary_and_deduplicated_by_content':True,'all_claim_declarations_and_SafeLearning_imports_resolve':True,'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(Path(__file__)),'errors':[],'limits':['This is an independent review of actual selection preparation/source/evidence/content retention only. It does not claim a fresh aggregate22 compiler, kernel or axiom pass.','Every baseline21 input/path/byte hash and actual old execution remains historical. The live integration is Root’s actual guarded copy, not a Lean compilation.','No original source, offer, ledger, review body/time, compiler record or current selection output was rewritten by this peer.']}
path=Path(out);assert not path.exists();path.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'path':out,'sha256':H(out),'counts':report['counts']}))
