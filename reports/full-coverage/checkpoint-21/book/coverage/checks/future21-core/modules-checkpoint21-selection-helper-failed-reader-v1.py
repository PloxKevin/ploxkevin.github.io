from pathlib import Path
import ast,json,hashlib,copy,re,tempfile,sys
from datetime import datetime,timezone
R=Path('/home/oxrexkevin/SafetyBased');HELP='book/coverage/prepare_checkpoint21_selection.py';src=(R/HELP).read_text();SH=hashlib.sha256(src.encode()).hexdigest();tree=ast.parse(src);cache={}
def H(n):
 p=Path(n);p=p if p.is_absolute() else R/p;s=p.stat();key=(str(p),s.st_size,s.st_mtime_ns)
 if key not in cache:cache[key]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[key]
def L(n):return json.loads((R/n).read_text())
# Evaluate only four read/guard functions, never production top-level mutation.
funcs=[n for n in tree.body if isinstance(n,ast.FunctionDef)];assert [n.name for n in funcs]==['read','sha','exact','actual_zero'];ns={'ROOT':R,'Path':Path,'hashlib':hashlib,'json':json};exec(compile(ast.Module(body=funcs,type_ignores=[]),HELP,'exec'),ns)
fixtures=[]
with tempfile.TemporaryDirectory(prefix='modules-selection21-guard-fixtures-',dir='/tmp') as td:
 F=Path(td);ns['ROOT']=F;source='verification/lean/SafeLearning/Fixture.lean';p=F/source;p.parent.mkdir(parents=True);p.write_text('namespace Fixture\nend Fixture\n');digest=hashlib.sha256(p.read_bytes()).hexdigest();lp=F/'output.log';lp.write_text('warning retained\n');lh=hashlib.sha256(lp.read_bytes()).hexdigest();rp=F/'actual.json'
 template={'source':source,'exit_code':0,'source_sha256_before':digest,'source_sha256_after':digest,'source_unchanged':True,'command':['lake','env','lean','SafeLearning/Fixture.lean'],'actual_workdir':str(F/'verification/lean'),'log_sha256':lh}
 def trial(label,mutate,pass_expected):
  d=copy.deepcopy(template);mutate(d);rp.write_text(json.dumps(d));e={'actual.json':hashlib.sha256(rp.read_bytes()).hexdigest(),'output.log':lh};passed=True
  try:assert ns['actual_zero'](source,digest,e)=='actual.json'
  except (AssertionError,KeyError):passed=False
  assert passed==pass_expected,(label,passed);fixtures.append({'fixture':label,'expected_accept':pass_expected,'actual_guard_result_matches':True})
 trial('genuine_standalone_record_exact_source_pair',lambda d:None,True)
 trial('original_missing_source_unchanged_supported_by_exact_pair',lambda d:d.pop('source_unchanged'),True)
 trial('explicit_false_source_unchanged_rejected',lambda d:d.update(source_unchanged=False),False)
 trial('changed_source_before_rejected',lambda d:d.update(source_sha256_before='0'*64),False)
 trial('changed_source_after_rejected',lambda d:d.update(source_sha256_after='0'*64),False)
 trial('actual_nonzero_exit_rejected',lambda d:d.update(exit_code=1),False)
 trial('named_only_build_not_standalone_rejected',lambda d:d.update(command=['lake','build','SafeLearning.Fixture']),False)
 trial('wrong_actual_workdir_rejected',lambda d:d.update(actual_workdir=td),False)
 trial('missing_actual_raw_log_digest_rejected',lambda d:d.update(log_sha256='1'*64),False)
 trial('different_source_record_rejected',lambda d:d.update(source='verification/lean/SafeLearning/Other.lean'),False)
ns['ROOT']=R
# Independently inspect the held real offers and every original standalone guard.
paths=['book/coverage/core-audit21-source48-additions-v1.json','book/coverage/applied-audit21-source48-additions-v1.json','book/coverage/foundations-audit21-source48-additions-v1.json','book/coverage/checks/modules-audit21-source48-additions-v1.json'];offers={n:L(n) for n in paths};baseline=L('reports/full-coverage/checkpoint-20-selection.json');selected=copy.deepcopy(baseline['proof_files']);new=set();actual={};offerhashes={n:H(n) for n in paths}
for n,o in offers.items():
 assert o['current_inventory_sha256']==H('book/coverage/inventory-after-correction48.json');ln=o.get('mapped_ledger',o.get('module_ledger'));assert H(ln)==o.get('mapped_ledger_sha256',o.get('module_ledger_sha256'))
 for p,h in o['source_sha256'].items():assert H(p)==h
 for p,row in o['proof_files'].items():
  assert H(p)==row['sha256'];ns['exact'](row['evidence_sha256'])
  if p not in selected:actual[p]=ns['actual_zero'](p,row['sha256'],row['evidence_sha256']);selected[p]=row;new.add(p)
  else:assert selected[p]['sha256']==row['sha256']
assert [len(offers[n]['proof_files']) for n in paths]==[9,5,7,0] and len(new)==21 and len(selected)==1089
for p,row in baseline['proof_files'].items():assert H(p)==row['sha256'];ns['exact'](row['evidence_sha256'])
for p,row in selected.items():
 for line in re.findall(r'^import[^\n]*',(R/p).read_text(),re.M):
  for dep in line.split()[1:]:
   if dep.startswith('SafeLearning.'):assert 'verification/lean/'+dep.replace('.','/')+'.lean' in selected,(p,dep)
m=offers[paths[-1]];assert set(m['required_external_import_dependencies'])<=set(selected);ns['exact'](m['required_external_import_dependencies']);assert not m['proof_files']
G='book/coverage/checks/root-source48-final-owner-integration21-v1.json';g=L(G);assert g['integrity_status']=='passed' and not g['errors'];assert g['inventory_sha256']==H('book/coverage/inventory-after-correction48.json')
for d in g['domains']:assert H('book/coverage/'+d['domain']+'.json')==d['ledger_sha256']
# Static review of only permitted production outputs and historical audit guards.
assert "audit['status'] == 'passed'" in src and 'assert audit[\'proof_sha256\'] ==' in src and "len(manifest['frozen_inputs_sha256']) == 30207" in src
assert "record['source_sha256_before'] == record['source_sha256_after'] == digest" in src and "record.get('source_unchanged', True) is True" in src
assert "selection = copy.deepcopy(baseline['proof_files'])" in src and "extras = copy.deepcopy(baseline['extra_frozen_inputs'])" in src
assert "assert sha('book/coverage/inventory.json') == inventory_hash" in src and "assert not destination.exists()" in src and 'coverage_complete=False' in src
assert "from retain_baseline_inputs21 import retain" in src and "frozen20-input-content-bindings21-v1.json" in src
assert src.count('.write_text(')==1 and "destination = ROOT/'reports/full-coverage/checkpoint-21-selection.json'" in src
assert "required_for_audit" in src and "{'.txt', '.cjs'}" in src and 'digest not in external_hashes' in src
assert not re.search(r'\b(subprocess|os\.system|exec_command|lake build)\b',src)
for n,h in offerhashes.items():assert H(n)==h
assert H(HELP)==SH
out='book/coverage/checks/future21-core/modules-checkpoint21-selection-helper-independent-confirmation-v1.json';assert not (R/out).exists();report={'status':'independent_checkpoint21_selection_helper_review_passed','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'selection_helper':HELP,'selection_helper_sha256':SH,'offers_sha256':offerhashes,'current_inventory':'book/coverage/inventory-after-correction48.json','current_inventory_sha256':H('book/coverage/inventory-after-correction48.json'),'global_integrity':G,'global_integrity_sha256':H(G),'counts':{'baseline_sources':1068,'actual_source_matched_new_sources':21,'candidate_selected_sources':1089,'core_new':9,'applied_new':5,'foundation_new':7,'modules_owned_new':0,'module_required_imports':len(m['required_external_import_dependencies']),'actual_isolated_guard_fixtures':len(fixtures)},'fixture_results':fixtures,'actual_original_standalone_records':actual,'production_selection_executed_by_peer':False,'read_only_source_ledger_and_package_scope':True,'baseline_content_retention_helper_peer':'book/coverage/checks/future21-core/modules-retain-baseline-inputs21-independent-helper-confirmation-v1.json','baseline_content_retention_helper_peer_sha256':H('book/coverage/checks/future21-core/modules-retain-baseline-inputs21-independent-helper-confirmation-v1.json'),'guard_review':['Every new source requires exact source-before/after SHA, actual standalone EXIT0, expected command/workdir and exact raw-log evidence. Missing historical unchanged flag is inferred only from the already checked exact pair; explicit False is rejected.','Baseline1068 source/evidence bytes remain exact, former successful audit is pinned as historical provenance, and selected import/declaration closure is checked against all four current held ledgers.','Only selection JSON and the separately independently reviewed retained-content output/aliases are written. No HTML, inventory, owner ledger, Lean source, package artifacts, theorem scopes or actual execution times are modified.','Full external primary papers stay reference-only; legitimate located txt/cjs are explicitly hash-scoped extras. Aggregate/kernel/axiom success is not claimed by preparation.'],'checker':str(Path(__file__)),'checker_sha256':H(Path(__file__)),'limits':['Independent helper review and actual isolated guard fixtures only. No production checkpoint21 preparation or frozen audit was executed by this checker. A separate actual output peer is required after root runs preparation.']};(R/out).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'path':out,'sha256':H(out),'counts':report['counts']}))
