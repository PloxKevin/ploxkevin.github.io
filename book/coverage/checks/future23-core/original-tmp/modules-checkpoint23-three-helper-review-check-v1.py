"""Readonly code review plus isolated synthetic validator fixtures, no production run."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,sys,importlib.util,tempfile,copy
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'));H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();ref=lambda p:{'file':str(Path(p).relative_to(R)) if Path(p).is_relative_to(R) else str(p),'sha256':H(p)}
helpers={'integration':'book/coverage/checks/root_integrate_owner23_candidates_v2.py','selector':'book/coverage/prepare_checkpoint23_selection_v1.py','live_interfaces':'book/coverage/prepare_checkpoint23_live_owner_interfaces_v2.py','retainer':'book/coverage/retain_baseline_inputs23.py'}
expected={'integration':'ccb69de25170b84a8262a08c4c339c496ae40d503c4e30c5d4441d16f45f74dd','selector':'5811fc10687074862bfbb273017eb72c2f8990b4e44a18a4f2cf05c7037a8f67','live_interfaces':'f3314d6f8a2263d91f06f5c80fdbe98195aed168697a86f2008c83f6ad237269'}
for k,p in helpers.items():
 ast.parse((R/p).read_text());assert k not in expected or H(R/p)==expected[k]
assert (R/helpers['retainer']).read_bytes()==(R/'book/coverage/retain_baseline_inputs22.py').read_bytes()
integration1=(R/'book/coverage/checks/root_integrate_owner23_candidates_v1.py').read_text();integration2=(R/helpers['integration']).read_text();assert integration1.replace('aggregate22_audit','aggregate23_audit')==integration2
live1=(R/'book/coverage/prepare_checkpoint23_live_owner_interfaces_v1.py').read_text();live2=(R/helpers['live_interfaces']).read_text();assert live1.replace('all34051_frozen21_inputs_exact','all34051_frozen22_inputs_exact').replace('all1113_selected21_root_source_hashes_exact','all1113_selected22_root_source_hashes_exact').replace('fresh22_audit','fresh23_audit')==live2
source51=R/'reports/full-coverage/source51-apply-execution-v1.json';actual=json.loads(source51.read_text());assert actual['actual_exit_code']==0 and H(R/actual['log'])==actual['log_sha256']
post=R/'book/coverage/checks/root-source-batch51/postwrite-source-integrity-v1.json';pj=json.loads(post.read_text());assert pj['actual_exit_code']==0 and pj['inventory_after_sha256']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
assert H(R/'book/coverage/inventory-after-correction51.json')==H(R/'book/coverage/inventory.json')==pj['inventory_after_sha256']
# Load selector definitions read-only; its guarded main is not executed.
spec=importlib.util.spec_from_file_location('independent_selector23_readonly',R/helpers['selector']);selector=importlib.util.module_from_spec(spec);spec.loader.exec_module(selector)
spec=importlib.util.spec_from_file_location('independent_live23_readonly',R/helpers['live_interfaces']);live=importlib.util.module_from_spec(spec);spec.loader.exec_module(live)
# Integration has deliberate top-level production code. Extract only its prefix definitions.
parsed=ast.parse(integration2);prefix=[]
for node in parsed.body:
 if isinstance(node,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='arguments' for x in node.targets):break
 prefix.append(node)
ns={'__file__':str(R/helpers['integration'])};exec(compile(ast.Module(body=prefix,type_ignores=[]),'readonly_integration_prefix','exec'),ns)
results=[]
def test(name,body,should_pass=True):
 try:body();passed=True
 except (AssertionError,KeyError,ValueError,FileNotFoundError):passed=False
 assert passed==should_pass,(name,passed,should_pass);results.append({'fixture':name,'expected_acceptance':should_pass,'actual_acceptance':passed})
with tempfile.TemporaryDirectory(prefix='module23-code-review-') as folder:
 root=Path(folder);selector.ROOT=root;live.ROOT=root;ns['ROOT']=root
 for label,safe in [('selector',selector.safe),('live',live.safe),('integration',ns['safe_path'])]:
  test(label+' canonical relative path',lambda safe=safe:safe('book/coverage/input.json'))
  test(label+' absolute rejected',lambda safe=safe:safe('/tmp/out.json'),False)
  test(label+' parent traversal rejected',lambda safe=safe:safe('../out.json'),False)
  outside=root.parent/'independent-outside-fixture';(root/'escape').symlink_to(outside)
  test(label+' symlink escape rejected',lambda safe=safe:safe('escape/out.json'),False);(root/'escape').unlink()
 for code in [0]:test('actual exit integer zero',lambda:selector.actual_exit_zero({'actual_exit_code':code}))
 for code in [1,True,None]:test('actual exit invalid '+repr(code),lambda code=code:selector.actual_exit_zero({'actual_exit_code':code}),False)
 test('actual dual exit aliases conflict',lambda:selector.actual_exit_zero({'actual_exit_code':0,'exit_code':1}),False)
 sname='verification/lean/SafeLearning/Fixture.lean';sp=root/sname;sp.parent.mkdir(parents=True);sp.write_text('-- synthetic parser validator fixture only\n');digest=H(sp)
 raw=root/'book/coverage/fixture.log';raw.parent.mkdir(parents=True);raw.write_text('synthetic nonexecution log\n');snapshot=root/'book/coverage/fixture-source.lean';snapshot.write_bytes(sp.read_bytes())
 record={'source':sname,'source_sha256_before':digest,'source_sha256_after':digest,'actual_exit_code':0,'actual_workdir':str(root/'verification/lean'),'source_snapshot_sha256':digest,'log_sha256':H(raw),'source_unchanged':True}
 def schema(mode='normal',change=None,standalone=True,named=True):
  evidence={'book/coverage/fixture.log':H(raw),'book/coverage/fixture-source.lean':digest}
  for label,cmd in [('standalone',['lake','env','lean','SafeLearning/Fixture.lean']),('named',['lake','build','SafeLearning.Fixture'])]:
   if (label=='standalone' and not standalone) or (label=='named' and not named):continue
   row={**copy.deepcopy(record),'command':cmd}
   if mode=='aliases':row['actual_command']=row.pop('command');row['exit_code']=row.pop('actual_exit_code');row['lean_file']=row.pop('source');row['raw_log_sha256']=row.pop('log_sha256');row['cwd']=row.pop('actual_workdir')
   if mode=='absolute' and label=='standalone':row['command'][-1]='/tmp/Fixture.lean';row['source']='/tmp/Fixture.lean'
   if mode=='lean-o' and label=='named':row['command']=['lake','env','lean','-o','SafeLearning/Fixture.olean','SafeLearning/Fixture.lean']
   if change:row.update(change)
   p=root/('book/coverage/fixture-'+label+'.json');p.write_text(json.dumps(row));evidence[str(p.relative_to(root))]=H(p)
  return evidence
 test('canonical genuine-record schema accepted',lambda:selector.standalone_success(sname,digest,schema()))
 test('historical original field aliases accepted',lambda:selector.standalone_success(sname,digest,schema('aliases')))
 test('historical absolute input requires exact snapshot accepted',lambda:selector.standalone_success(sname,digest,schema('absolute')))
 test('named lean-o pair schema accepted',lambda:selector.standalone_success(sname,digest,schema('lean-o')))
 test('named only never substitutes standalone',lambda:selector.standalone_success(sname,digest,schema(standalone=False)),False)
 test('standalone only missing named rejected',lambda:selector.standalone_success(sname,digest,schema(named=False)),False)
 test('source unchanged false rejected',lambda:selector.standalone_success(sname,digest,schema(change={'source_unchanged':False})),False)
 test('nonzero compiler rejected',lambda:selector.standalone_success(sname,digest,schema(change={'actual_exit_code':1})),False)
 test('wrong source digest rejected',lambda:selector.standalone_success(sname,digest,schema(change={'source_sha256_after':'0'*64})),False)
 test('wrong compiler working directory rejected',lambda:selector.standalone_success(sname,digest,schema(change={'actual_workdir':'/tmp'})),False)
 test('unbound rawlog hash rejected',lambda:selector.standalone_success(sname,digest,schema(change={'log_sha256':'0'*64})),False)
 test('unbound source snapshot rejected',lambda:selector.standalone_success(sname,digest,schema(change={'source_snapshot_sha256':'0'*64})),False)
 # Pure retainer fixture uses mock prior manifest content, not an actual audit.
 src='proof.lean';(root/src).write_text('synthetic proof fixture\n');d=H(root/src);snapshotname='reports/full-coverage/prior-fixture';fr=root/snapshotname;fr.mkdir(parents=True);(fr/'proof.lean').write_bytes((root/src).read_bytes());(fr/'older.log').write_text('unseen historical bytes\n');oldhash=H(fr/'older.log')
 baseline={'status':'synthetic_requires_fresh_aggregate_audit','proof_files':{src:{'sha256':d,'evidence_sha256':{}}},'extra_frozen_inputs':{}}
 bp='reports/full-coverage/baseline-fixture.json';(root/bp).write_text(json.dumps(baseline));mp='reports/full-coverage/manifest-fixture.json';(root/mp).write_text(json.dumps({'status':'formal_verification_passed_partial_coverage','selection':bp,'selection_sha256':H(root/bp),'proof_files':baseline['proof_files'],'snapshot':snapshotname,'frozen_inputs_sha256':{'proof.lean':d,'older.log':oldhash}}));selected=copy.deepcopy(baseline['proof_files']);mapped='book/coverage/content-fixture.json'
 test('retainer exact-by-content prior bytes',lambda:selector.retain(root,bp,mp,selected,{},mapped));mapping=json.loads((root/mapped).read_text());assert mapping['original_input_count']==2 and mapping['retained_existing_content_rows']==1 and mapping['new_unique_snapshot_alias_count']==1
 selected=copy.deepcopy(baseline['proof_files']);selected[src]['sha256']='0'*64;test('retainer changed baseline source rejected',lambda:selector.retain(root,bp,mp,selected,{},'book/coverage/invalid-content.json'),False)
report={'status':'independent_root23_integration_selector_and_live_interface_code_review_passed','reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(R/helpers['integration']),'helper_sha256':H(R/helpers['integration']),'helpers':{k:ref(R/p) for k,p in helpers.items()},'fixture_results':results,'fixture_count':len(results),'draft_v1_findings_preserved':{'integration':ref(R/'book/coverage/checks/root_integrate_owner23_candidates_v1.py'),'live_interfaces':ref(R/'book/coverage/prepare_checkpoint23_live_owner_interfaces_v1.py'),'findings':['Integration producer status said aggregate22 while live consumer required23.','Live consumer read frozen21/selected21 field names from a frozen22/selected22 producer.','Appended live interface label said fresh22 audit.'],'decision':'Original draft pair not ready for execution. NEWv2 changes only these exact checkpoint-label/schema strings, all underlying protection/copy guards unchanged.'},'source51_actual_prerequisite':ref(source51),'source51_postwrite':ref(post),'retainer_byte_identical_to_independently_reviewed22':True,'guard_review':['Read-only default versus explicit --apply, actual source51 prerequisite, frozen22 34051/current1113 and current51asset distinction, reviewed candidate/semantic peer/time/builder0 provenance, only four owner ledgers plus Applied promotions destinations, archived original22 bytes and atomic per-file exactcopy.','Live offers reverse exactly to whole candidate offers and preserve their source scopes; integration actual0 command/hash/log/result/archive required, fresh current global0 and separate independent interface peer required before a plan.','Selector pins installed four ledgers/global0/owner peers/current51; validates both true standalone and named schemas, log/snapshot by content, baseline exactproof/evidence, local declaration/import closure, full-reference exclusions and unchanged original frozen inputs via by-content history map.'],'actual_checker':ref(Path(__file__)),'errors':[],'limits':['Code mechanics review and isolated synthetic acceptance/rejection fixtures only. No integration helper, plan preparation, production selector, actual compiler or site publication was executed by this reviewer.','Actual final four-owner binding manifest, installed offers/interfaces, selection plan and resulting production selection/content map still require separate exact output peers.','Synthetic fixture records never represent real compiler or audit executions.']}
out=Path('/tmp/root23-three-helpers-independent-modules-code-review-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':report['status'],'report':str(out),'sha256':H(out),'fixtures':len(results)}))
