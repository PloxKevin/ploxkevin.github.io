from pathlib import Path
import json,hashlib,re,sys
from datetime import datetime,timezone
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations
cache={}
def safe(n):
 p=Path(n);assert isinstance(n,str) and n and not p.is_absolute() and '..' not in p.parts and str(p)==n and (R/p).resolve().is_relative_to(R.resolve()),n
 return R/p
def H(n):
 p=Path(n);p=p if p.is_absolute() else safe(n);st=p.stat();k=(str(p.resolve()),st.st_size,st.st_mtime_ns)
 if k not in cache:cache[k]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[k]
def L(n):return json.loads(safe(n).read_text())
S='reports/full-coverage/checkpoint-21-selection.json';s=L(S);sn=H(S);assert s['proof_file_count']==len(s['proof_files'])==1089 and s['new_file_count']==21 and s['coverage_complete'] is False
assert s['status']=='explicit_current48_source_matched_selection_requires_fresh_aggregate_audit' and not s['deliberate_baseline_source_revisions']
HELP='book/coverage/prepare_checkpoint21_selection_v2.py';assert H(HELP)=='2f8acc863d97d261541098d947159d320cbadb0909db025386c56f11368d085c';hp='book/coverage/checks/future21-core/modules-checkpoint21-selection-helper-independent-confirmation-v2.json';h=L(hp);assert h['selection_helper_sha256']==H(HELP)
# Locate exactly the actual root production execution, retaining its original command/times/raw log.
execs=['reports/full-coverage/prepare-checkpoint21-selection-execution-v2.json']
assert len(execs)==1;en=execs[0];e=L(en);assert e['status']=='passed' and e['actual_exit_code']==0 and e['actual_command'] in [['python3',HELP],['python',HELP]] and e['actual_workdir']==str(R);assert e['helper_sha256_before']==e['helper_sha256_after'] and e['helper_sha256_before'][HELP]==H(HELP) and e['selection_sha256']==sn;assert H(e['log'])==e['log_sha256']
base=L(s['baseline_selection']);assert H(s['baseline_selection'])==s['baseline_selection_sha256'];audit=L(s['actual_passing_baseline_audit']);assert H(s['actual_passing_baseline_audit'])==s['actual_passing_baseline_audit_sha256'] and audit['status']=='passed'
assert len(base['proof_files'])==1068;new=set(s['proof_files'])-set(base['proof_files']);assert len(new)==21
for p,row in base['proof_files'].items():
 now=s['proof_files'][p]
 for k,v in row.items():
  if k=='evidence_sha256':assert all(now[k].get(a)==hh for a,hh in v.items()),p
  elif k=='inherited_snapshot_provenance_scope' and p==sorted(base['proof_files'])[0]:assert now[k]=='Every frozen20 input is retained by the separate exact original path/content binding map; identical byte sequences share immutable selected inputs. Original actual executions remain historical.'
  else:assert now[k]==v,(p,k)
 assert set(now)-set(row)<={'inherited_snapshot_provenance_scope'}
 assert H(p)==row['sha256']
 for a,hh in row['evidence_sha256'].items():assert H(a)==hh
for p,row in base['extra_frozen_inputs'].items():assert s['extra_frozen_inputs'][p]==row
for n,hh in s['offers_sha256'].items():assert H(n)==hh==h['offers_sha256'][n]
offers={n:L(n) for n in s['offers_sha256']};offered={p:r for o in offers.values() for p,r in o['proof_files'].items()};assert set(offered)==new and len(offered)==21
for p,row in offered.items():
 got=s['proof_files'][p];assert H(p)==row['sha256']
 for k,v in row.items():assert got[k]==v,(p,k)
 n=got['original_actual_zero_record'];a=L(n);assert n in row['evidence_sha256'] and a['source']==p and a['exit_code']==0 and a['source_sha256_before']==a['source_sha256_after']==row['sha256'];assert a.get('source_unchanged',True) is True
 assert a.get('command',a.get('actual_command'))==['lake','env','lean',str(Path(p).relative_to('verification/lean'))] and Path(a['actual_workdir']).resolve()==(R/'verification/lean').resolve()
 assert any(q.endswith('.log') and hh==a['log_sha256'] for q,hh in row['evidence_sha256'].items())
bound={}
for p,row in s['proof_files'].items():
 assert H(p)==row['sha256'];bound[p]=row['sha256']
 for q,hh in row['evidence_sha256'].items():assert H(q)==hh;assert q not in bound or bound[q]==hh;bound[q]=hh
 for line in re.findall(r'^import[^\n]*',safe(p).read_text(),re.M):
  for dep in line.split()[1:]:
   if dep.startswith('SafeLearning.'):assert 'verification/lean/'+dep.replace('.','/')+'.lean' in s['proof_files'],(p,dep)
for p,row in s['extra_frozen_inputs'].items():assert H(p)==row['sha256'];assert p not in bound or bound[p]==row['sha256'];bound[p]=row['sha256']
pr=s['previous_frozen_input_content_binding'];pn=pr['file'];assert H(pn)==pr['sha256'];pm=L(pn);old=L(pm['baseline_manifest']);assert H(pm['baseline_manifest'])==pm['baseline_manifest_sha256'];assert pm['baseline_selection']==s['baseline_selection'] and pm['baseline_selection_sha256']==s['baseline_selection_sha256'];assert len(old['frozen_inputs_sha256'])==pm['original_input_count']==pr['original_inputs']==30207
rows=pm['input_bindings'];assert len(rows)==30207;assert {r['original_frozen_path']:r['sha256'] for r in rows}==old['frozen_inputs_sha256'];seen={}
for r in rows:
 p=r['original_frozen_path'];safe(p);target=r['retained_input'];safe(target);digest=r['sha256'];assert H(str(Path(old['snapshot'])/p))==digest==H(target)==bound[target]
 assert digest not in seen or seen[digest]==target;seen[digest]=target
aliases=pm['new_unique_snapshot_aliases'];assert len(aliases)==pm['new_unique_snapshot_alias_count']==pr['new_snapshot_aliases'];assert pm['retained_existing_content_rows']+len(aliases)==30207;assert sum(safe(n).stat().st_size for n in aliases)==pm['new_unique_snapshot_alias_bytes'];assert len(set(aliases.values()))==len(aliases)
first=s['proof_files'][sorted(s['proof_files'])[0]]
for n,hh in aliases.items():assert n.startswith(old['snapshot']+'/') and H(n)==hh and first['evidence_sha256'][n]==hh
initialbound={n:hh for n,hh in bound.items() if n not in aliases and n!=pn}
assert not set(aliases.values())&set(initialbound.values()),'unnecessary duplicate snapshot alias'
# Required local passages and executed harnesses remain explicit; full external papers remain references.
dep19=L('book/coverage/checks/modules-source44-canonical-dependency-manifest19-v1.json');required=[r for r in dep19['artifacts'] if r['required_for_execution_or_immutable_provenance_freeze'] and Path(r['path']).suffix in ['.txt','.cjs']];assert len(required)==49
for r in required:assert s['extra_frozen_inputs'][r['path']]['sha256']==r['sha256']==H(r['path'])
fullpaper={r['sha256'] for r in dep19['artifacts'] if r['type']=='external_primary_paper_reference'}
mo=next(o for o in offers.values() if 'module_ledger' in o);dep=L(mo['canonical_dependency_manifest']['file']);fullpaper|={r['sha256'] for r in dep['primary_references']};assert not fullpaper&{r['sha256'] for r in s['extra_frozen_inputs'].values()}
G=s['global_integrity'];assert H(G)==s['global_integrity_sha256'];g=L(G);assert g['integrity_status']=='passed' and not g['errors'] and g['inventory_sha256']==s['current_inventory_sha256']==H(s['current_inventory'])==H('book/coverage/inventory.json');allnames={d['name'] for p in s['proof_files'] for d in declarations(safe(p).read_text())}
for d in g['domains']:
 ln='book/coverage/'+d['domain']+'.json';assert H(ln)==d['ledger_sha256'];l=L(ln)
 for c in l['material_claims']+[c for x in l['exercises'] for c in x['claims']]:assert set(c['lean_declarations'])<=allnames,(ln,c['id'])
assert set(mo['required_external_import_dependencies'])<=set(s['proof_files']);assert H(S)==sn and H(HELP)==h['selection_helper_sha256']
out=Path('/tmp/modules-checkpoint21-actual-selection-and-content-map-independent-confirmation-v1.json');assert not out.exists();report={'status':'independent_actual_checkpoint21_selection_and_retained_content_confirmation_passed','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'selection':S,'selection_sha256':sn,'actual_production_execution':en,'actual_production_execution_sha256':H(en),'selection_helper':HELP,'selection_helper_sha256':H(HELP),'independent_helper_peer':hp,'independent_helper_peer_sha256':H(hp),'preserved_failed_reader':'/tmp/modules-checkpoint21-production-output-failed-reader-v1.json','baseline_content_binding':pn,'baseline_content_binding_sha256':H(pn),'offers_sha256':s['offers_sha256'],'current_inventory':s['current_inventory'],'current_inventory_sha256':s['current_inventory_sha256'],'global_integrity':G,'global_integrity_sha256':H(G),'counts':{'baseline_selected_sources':1068,'actual_source_matched_new_sources':21,'selected_sources':1089,'original_frozen20_input_paths_and_bytes':30207,'distinct_original_frozen_byte_hashes':len(seen),'new_unique_snapshot_aliases':len(aliases),'new_unique_snapshot_alias_bytes':pm['new_unique_snapshot_alias_bytes'],'retained_existing_content_rows':pm['retained_existing_content_rows'],'required_located_primary_text_and_executed_cjs':49,'full_primary_reference_hashes_excluded_from_extras':len(fullpaper),'extra_frozen_inputs':len(s['extra_frozen_inputs']),'module_required_imports':len(mo['required_external_import_dependencies'])},'baseline_original_source_evidence_commands_times_unchanged':True,'only_first_source_current_inherited_content_scope_reworded':True,'each_original_frozen_path_hash_resolves_to_exact_selected_evidence_source_or_extra':True,'every_new_unique_snapshot_alias_is_necessary_and_duplicate_hashes_share_one_path':True,'all_current_ledger_declarations_and_all_selected_imports_closed':True,'checker':str(Path(__file__)),'checker_sha256':H(Path(__file__)),'limits':['This independently verifies actual preparation outputs and source/evidence/content identity. The preparation is not a checkpoint21 compiler/kernel/axiom pass. Fresh frozen verification is required.','The previous checkpoint20 actual audit and30207 frozen inputs are preserved as historical provenance, with every original path/hash explicit. No original execution or mathematical review body/time was rewritten.']};out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'path':str(out),'sha256':H(out),'counts':report['counts']}))
