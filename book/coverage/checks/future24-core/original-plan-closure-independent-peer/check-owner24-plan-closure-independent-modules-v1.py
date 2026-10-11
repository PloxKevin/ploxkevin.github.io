"""Independent code/isolated-fixture review; never run the Root production closer."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,tempfile,subprocess,copy,ast
R=Path('/home/oxrexkevin/SafetyBased')
HELPER='book/coverage/checks/root_close_checkpoint24_selection_plan_v1.py'
BASE='book/coverage/checks/future24-core'
OUT=Path('/tmp/owner24-plan-closure-independent-modules-code-review-v1.json')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=(R/HELPER).read_bytes();assert H(R/HELPER)=='9dbcd6a8086717e1710efe9da3c20bbcf7a25e130d90887af5b1cb863dad7b20'
assert not OUT.exists();ast.parse(source)
assert b'subprocess' not in source and b'shutil' not in source
assert b"with (ROOT/NEW).open('x')" in source and b"with (ROOT/target).open('xb')" in source
stems=['prepare-owner24-interface-request-execution-v1','prepare-owner24-live-interfaces-execution-v1','prepare-owner24-selection-plan-execution-v1']
fixtures=[]
def fixture(mode):
 with tempfile.TemporaryDirectory(prefix='owner24-closure-review-') as tmp:
  root=Path(tmp);helper=root/HELPER;helper.parent.mkdir(parents=True);helper.write_bytes(source)
  base=root/BASE;base.mkdir();(root/'reports/full-coverage').mkdir(parents=True)
  def write(n,b):
   p=root/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return p
  def jsonwrite(n,d):return write(n,(json.dumps(d,indent=2)+'\n').encode())
  peer='book/coverage/checks/pages24-config-helper-independent-foundations-review-v1.json'
  jsonwrite(peer,{'status':'passed','original_review_time':'unchanged'})
  jsonwrite(BASE+'/late-peer.json',{'status':'passed','original_time':'same'})
  write(BASE+'/late-reader.py',b'# closed independent reader\n')
  write(BASE+'/__pycache__/excluded.pyc',b'not allowed cache')
  old={'status':'independently_reviewed_installed_owner24_selection_plan','owners':{'core':{'original_review_time':'2026-10-11T00:00:00+00:00','source_hash':'kept'},'modules':{'proofs':[1,2,3]}},'helpers_sha256':{'original.py':'unchanged'},'additional_frozen_inputs':{},'excluded_full_external_reference_sha256':[],'authorized_baseline_owner_evidence_aliases':{'exact_four':'unchanged'},'inventory':{'sha256':'38518673'},'old_plan_time':'original'}
  for i,stem in enumerate(stems):
   log='reports/full-coverage/'+stem+'.log';lp=write(log,('actual log '+str(i)+'\n').encode())
   row={'actual_exit_code':0,'log':log,'log_sha256':H(lp),'actual_command':['python3','actual-helper-'+str(i)],'started_at_utc':'native-start-'+str(i),'finished_at_utc':'native-finish-'+str(i)}
   if mode=='nonzero' and i==1:row['actual_exit_code']=1
   if mode=='wrong_log' and i==1:row['log_sha256']='0'*64
   if not (mode=='missing_record' and i==1):jsonwrite('reports/full-coverage/'+stem+'.json',row)
  if mode=='excluded_full_reference':old['excluded_full_external_reference_sha256']=[H(root/(BASE+'/late-peer.json'))]
  if mode=='conflicting_extra':old['additional_frozen_inputs'][BASE+'/late-peer.json']={'sha256':'0'*64,'scope':'immutable_audit_or_local_source_evidence'}
  oldp=jsonwrite(BASE+'/checkpoint24-installed-owner-selection-plan-v1.json',old);original=oldp.read_bytes()
  new=root/(BASE+'/checkpoint24-installed-owner-selection-plan-v2.json')
  if mode=='existing_plan':new.write_bytes(b'previous final plan');preserved=new.read_bytes()
  if mode=='existing_selection':write('reports/full-coverage/checkpoint-24-selection.json',b'previous selection')
  before={n: (root/n).read_bytes() for n in [str(oldp.relative_to(root)),peer,BASE+'/late-peer.json',BASE+'/late-reader.py']}
  run=subprocess.run(['python3',str(helper)],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  assert oldp.read_bytes()==original
  for n,b in before.items():assert (root/n).read_bytes()==b
  if mode=='accept':
   assert run.returncode==0,run.stdout.decode();out=json.loads(new.read_text())
   assert out['entire_original_installed_owner_selection_plan_v1_body_and_time']==old
   assert out['original_installed_owner_selection_plan_v1']=={'file':str(oldp.relative_to(root)),'sha256':H(oldp)}
   inverse=copy.deepcopy(out)
   for key in ['original_installed_owner_selection_plan_v1','entire_original_installed_owner_selection_plan_v1_body_and_time','closed_interface_and_plan_original_byte_aliases','plan_closure_prepared_at_utc']:inverse.pop(key)
   inverse['additional_frozen_inputs']=old['additional_frozen_inputs'];inverse['helpers_sha256']=old['helpers_sha256'];assert inverse==old
   cat=out['closed_interface_and_plan_original_byte_aliases'];cp=root/cat['file'];assert H(cp)==cat['sha256'];catalog=json.loads(cp.read_text());assert len(catalog['aliases'])==6
   for alias in catalog['aliases']:
    a,b=alias['original'],alias['immutable_original_byte_copy'];assert (root/a['file']).read_bytes()==(root/b['file']).read_bytes();assert H(root/a['file'])==a['sha256']==b['sha256']
   for n,row in out['additional_frozen_inputs'].items():assert H(root/n)==row['sha256'];assert '__pycache__' not in n
   assert str(new.relative_to(root)) not in out['additional_frozen_inputs']
   assert out['helpers_sha256'][HELPER]==H(helper)
  else:
   assert run.returncode!=0,mode
   if mode=='existing_plan':assert new.read_bytes()==preserved
   else:assert not new.exists(),mode
  fixtures.append({'case':mode,'accepted':mode=='accept','actual_isolated_exit_code':run.returncode,'original_inputs_unchanged':True})
for mode in ['accept','nonzero','wrong_log','missing_record','existing_plan','existing_selection','excluded_full_reference','conflicting_extra']:fixture(mode)
actual_files=[p for p in (R/BASE).rglob('*') if p.is_file() and '__pycache__' not in p.parts]
assert all(p.suffix in {'.json','.py','.log','.lean','.md'} for p in actual_files)
assert H(R/HELPER)=='9dbcd6a8086717e1710efe9da3c20bbcf7a25e130d90887af5b1cb863dad7b20'
row={'status':'independent_checkpoint24_closed_plan_evidence_helper_code_and_fixtures_passed','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':HELPER,'sha256':H(R/HELPER)},'helper_sha256':H(R/HELPER),'fixtures':fixtures,'actual_current_core_closure_suffixes':sorted({p.suffix for p in actual_files}),'actual_current_core_closure_files_observed':len(actual_files),'entire_prior_plan_reverse_exact':True,'actual_closed_command_time_status_log_bytes_preserved':True,'explicit_late_closure_root':BASE,'errors':[],'coverage_complete':False,'scope':'Independent full code and isolated temporary fixtures only. The production closer was not imported or executed, no Root plan/interfaces/selection or owner assets written. Its exact bounded current future24-core file set contains only freezer-supported audit/helper/proof extensions, skips caches, rejects excluded full references/conflicts, and creates a new reversible plan2. Actual future production output requires its own measured record.'}
OUT.write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({'report':str(OUT),'sha256':H(OUT),'fixtures':len(fixtures)}))
