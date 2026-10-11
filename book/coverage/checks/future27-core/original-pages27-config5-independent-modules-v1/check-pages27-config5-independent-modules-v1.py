from pathlib import Path
from datetime import datetime,timezone
from types import SimpleNamespace
import ast,hashlib,json,importlib.util,tempfile,subprocess,os,copy
R=Path('/home/oxrexkevin/SafetyBased');N='book/coverage/checks/root_prepare_pages27_config_v5.py';P=R/N;OLD='book/coverage/checks/root_prepare_pages27_config_v4.py';PREV='book/coverage/checks/pages27-config-helper-independent-modules-review-v4.json';OUT=Path('/tmp/pages27-config5-independent-modules-check-result-v1.json');assert not OUT.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P)=='d7e2a4764f4678d6e7dc7c6443a732fc60224b733633db3a1646628801ebd101';assert sha(R/OLD)=='9f9f683d3400d071b089876f834711d07c9ecc172b6bd39d6277e0a6cfc85f44'
previous=json.loads((R/PREV).read_bytes());assert previous['status']=='requires_real_website_budget_repair_before_native_preparation' and previous['code_review_status'].startswith('passed')
for n,h in previous['closed_evidence_sha256'].items():assert sha(R/n)==h,n
oldtree=ast.parse((R/OLD).read_text());newtree=ast.parse(P.read_text());normalize=lambda n:ast.dump(n,include_attributes=False)
# Full code unchanged outside exact literal archive constants, prepare archival
# map/count/report fields, SELF name and final count output. Compare each node.
oldnodes={getattr(n,'name',str(i)):n for i,n in enumerate(oldtree.body)};newnodes={getattr(n,'name',str(i)):n for i,n in enumerate(newtree.body)}
oldfunc={n.name:n for n in oldtree.body if isinstance(n,(ast.FunctionDef,ast.ClassDef))};newfunc={n.name:n for n in newtree.body if isinstance(n,(ast.FunctionDef,ast.ClassDef))};assert set(oldfunc)==set(newfunc)
for name in oldfunc:
 if name not in ['prepare','main']:assert normalize(oldfunc[name])==normalize(newfunc[name]),name
# Reverse only authorized AST statements/fields to recover entire parent AST.
a=copy.deepcopy(newtree)
remove=[]
for i,n in enumerate(a.body):
 if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id in ['RETIRED_OLD_DELIVERY_FILES','RETIRED_OLD_AUDIT_DIR'] for t in n.targets):remove.append(i)
 if isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name) and n.target.id=='NEW_LITERAL_EXCLUSIONS':remove.append(i)
for i in reversed(remove):a.body.pop(i)
for n in ast.walk(a):
 if isinstance(n,ast.Constant) and n.value==129:n.value=124
 if isinstance(n,ast.Constant) and n.value=='book/coverage/checks/root_prepare_pages27_config_v5.py':n.value=OLD
 if isinstance(n,ast.Compare) and isinstance(n.left,ast.Call) and isinstance(n.left.func,ast.Name) and n.left.func.id=='len' and n.left.args and isinstance(n.left.args[0],ast.Name) and n.left.args[0].id=='NEW_LITERAL_EXCLUSIONS':n.comparators[0]=ast.Constant(value=8)
q=next(n for n in a.body if isinstance(n,ast.FunctionDef) and n.name=='prepare');op=oldfunc['prepare']
start=next(i for i,n in enumerate(q.body) if isinstance(n,ast.For) and isinstance(n.iter,ast.Call) and isinstance(n.iter.func,ast.Attribute) and isinstance(n.iter.func.value,ast.Name) and n.iter.func.value.id=='RETIRED_OLD_DELIVERY_FILES')
end=next(i for i,n in enumerate(q.body[start:],start) if isinstance(n,ast.For) and isinstance(n.iter,ast.Call) and isinstance(n.iter.func,ast.Attribute) and isinstance(n.iter.func.value,ast.Name) and n.iter.func.value.id=='DUPLICATE_INVENTORIES');del q.body[start:end]
for i,n in enumerate(q.body):
 if isinstance(n,ast.Assert) and isinstance(n.test,ast.UnaryOp) and isinstance(n.test.operand,ast.Call) and isinstance(n.test.operand.func,ast.Name) and n.test.operand.func.id=='kept':
  q.body[i]=copy.deepcopy(next(z for z in op.body if isinstance(z,ast.Assert) and isinstance(z.test,ast.Call) and isinstance(z.test.func,ast.Name) and z.test.func.id=='kept' and any(isinstance(x,ast.Constant) and x.value=='reports/full-coverage/browser-artifacts-25/example.png' for x in ast.walk(z))))
reportnode=next(n for n in q.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='report' for t in n.targets));oldreport=next(n for n in op.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='report' for t in n.targets));keys={'older_delivery_file_archives_sha256','older25_audit_archives_sha256','older_retired_archives_all_root_publication_tracked_HEAD_exact'}
newdict=reportnode.value
for i in reversed(range(len(newdict.keys))):
 if isinstance(newdict.keys[i],ast.Constant) and newdict.keys[i].value in keys:newdict.keys.pop(i);newdict.values.pop(i)
for i,k in enumerate(newdict.keys):
 if isinstance(k,ast.Constant) and k.value=='scope':newdict.values[i]=copy.deepcopy(oldreport.value.values[next(j for j,z in enumerate(oldreport.value.keys) if isinstance(z,ast.Constant) and z.value=='scope')])
assert normalize(a)==normalize(oldtree),'entire parent AST restored by exact authorized5 delta'
spec=importlib.util.spec_from_file_location('pages27config5_independent',P);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);assert len(m.NEW_LITERAL_EXCLUSIONS)==13 and len(m.RETIRED_OLD_DELIVERY_FILES)==4
base=Path(tempfile.mkdtemp(prefix='pages27-config5-archive-fixtures-'));froot=base/'root';fpub=base/'pub';froot.mkdir();fpub.mkdir();fixtures=[]
def good(name):fixtures.append({'name':name,'result':'passed','scope':'isolated code fixture, no real configuration producer'})
def reject(name,fn):
 try:fn()
 except(AssertionError,subprocess.CalledProcessError):good(name);return
 raise AssertionError('unexpected accepted '+name)
n='old/archive.json'
for r in [froot,fpub]:(r/'old').mkdir();(r/n).write_bytes(b'exact')
subprocess.run(['git','init','-q'],cwd=fpub,check=True);subprocess.run(['git','add','--',n],cwd=fpub,check=True);subprocess.run(['git','-c','user.name=Isolated Fixture','-c','user.email=fixture@example.invalid','-c','commit.gpgsign=false','commit','-qm','isolated old bytes'],cwd=fpub,check=True)
h=sha(froot/n);m.tracked_exact(froot,fpub,n,h);good('real_tracked_root_pub_HEAD_exact_file_accept')
for r,name in [(froot,'root_digest_drift_reject'),(fpub,'pub_digest_drift_reject')]:
 (r/n).write_bytes(b'drift');reject(name,lambda:m.tracked_exact(froot,fpub,n,h));(r/n).write_bytes(b'exact')
for r in [froot,fpub]:(r/n).write_bytes(b'both changed')
reject('same_root_pub_changed_HEAD_bytes_reject',lambda:m.tracked_exact(froot,fpub,n,sha(froot/n)))
for r in [froot,fpub]:(r/n).write_bytes(b'exact')
u='old/untracked.json'
for r in [froot,fpub]:(r/u).write_bytes(b'exact')
reject('untracked_old_archive_reject',lambda:m.tracked_exact(froot,fpub,u,h))
(froot/n).unlink();(froot/n).symlink_to(froot/u);reject('retired_archive_file_symlink_reject',lambda:m.tracked_exact(froot,fpub,n,h));(froot/n).unlink();(froot/n).write_bytes(b'exact')
# Isolate original prepare's exact retirement map/size/tracked-set gate nodes.
body=newfunc['prepare'].body;i=next(i for i,z in enumerate(body) if isinstance(z,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='old_audit_root' for t in z.targets));j=next(j for j,z in enumerate(body[i:],i) if isinstance(z,ast.For) and isinstance(z.iter,ast.Call) and isinstance(z.iter.func,ast.Attribute) and isinstance(z.iter.func.value,ast.Name) and z.iter.func.value.id=='DUPLICATE_INVENTORIES');gate=body[i:j];groot=base/'dir-root';gpub=base/'dir-pub'
for r in [groot,gpub]:
 (r/m.RETIRED_OLD_AUDIT_DIR).mkdir(parents=True)
 for index in range(1165):(r/m.RETIRED_OLD_AUDIT_DIR/('f'+str(index)+'.json')).write_bytes(str(index).encode())
names={p.relative_to(gpub).as_posix() for p in (gpub/m.RETIRED_OLD_AUDIT_DIR).iterdir()};tracking={'names':set(names)};seen=[]
def mock_run(cmd,**kw):assert cmd==['git','ls-files','-z','--',m.RETIRED_OLD_AUDIT_DIR] and kw['cwd']==gpub;return SimpleNamespace(stdout=('\0'.join(sorted(tracking['names']))+'\0').encode())
def gate_run():
 ns=dict(m.__dict__);ns.update(root=groot,pub=gpub,subprocess=SimpleNamespace(run=mock_run),tracked_exact=lambda a,b,n,h:seen.append((n,h)));exec(compile(ast.Module(body=gate,type_ignores=[]),str(P),'exec'),ns);return ns
ns=gate_run();assert len(seen)==1165 and ns['old_audit_root']==ns['old_audit_pub'];good('exact1165_retired_directory_paths_and_tracked_set_accept')
x=groot/m.RETIRED_OLD_AUDIT_DIR/'extra.json';x.write_bytes(b'extra');reject('additional_retired_directory_regular_file_reject',gate_run);x.unlink()
x=groot/m.RETIRED_OLD_AUDIT_DIR/'f0.json';b=x.read_bytes();x.unlink();reject('missing_retired_directory_file_reject',gate_run);x.write_bytes(b)
x=gpub/m.RETIRED_OLD_AUDIT_DIR/'f0.json';b=x.read_bytes();x.write_bytes(b'drift');reject('samecount_retired_pub_digest_drift_reject',gate_run);x.write_bytes(b)
tracking['names'].remove(next(iter(names)));reject('retired_directory_tracked_set_missing_reject',gate_run);tracking['names']=set(names)|{'extra/unapproved'};reject('retired_directory_tracked_set_extra_reject',gate_run);tracking['names']=set(names)
# Complete REAL native read-only prepare, strict byte budget includes output3.
protected={n:sha(R/n) for n in ['book/coverage/inventory.json','book/coverage/material-corrections.json','book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json',N,OLD,PREV]};before=sha(m.PUB/'_config.yml');old,after,report,outputs=m.prepare()
assert sha(m.PUB/'_config.yml')==before==m.BEFORE and report['helper']=={'file':N,'sha256':sha(P)} and report['excluded_count']==129 and len(report['new_literal_exclusions'])==13 and report['selected_sources']==1175 and report['theorem_exports']==9644 and len(report['required_publication_files_sha256'])==1284
assert len(report['older25_audit_archives_sha256'])==1165 and report['older_delivery_file_archives_sha256']==m.RETIRED_OLD_DELIVERY_FILES and report['older_retired_archives_all_root_publication_tracked_HEAD_exact'] is True
assert report['prospective_included_website_bytes_including_native_records']==report['prospective_included_website_bytes_before_new_native_records']+sum(map(len,outputs.values()))<850000000
for r in [R,m.PUB]:
 for n in outputs:assert not (r/n).exists()
count=0
for top,dirs,files in os.walk(m.PUB,followlinks=False):
 root=Path(top)
 for dn in list(dirs):
  q=root/dn;n=q.relative_to(m.PUB).as_posix()
  if '.git' in q.relative_to(m.PUB).parts or not m.kept(n,set(report['exclusions'])):dirs.remove(dn);continue
  assert not q.is_symlink(),n
 for fn in files:
  q=root/fn;n=q.relative_to(m.PUB).as_posix()
  if not m.kept(n,set(report['exclusions'])):continue
  assert not q.is_symlink(),n;count+=q.stat().st_size
assert count-len(old)+len(after)==report['prospective_included_website_bytes_before_new_native_records'];good('real_native_full_prepare_and_independent_exact_included_byte_budget_pass')
for n,h in protected.items():assert sha(R/n)==h,n
retirebytes=sum((R/n).stat().st_size for n in report['older25_audit_archives_sha256']);deliverybytes=sum((R/n).stat().st_size for n in m.RETIRED_OLD_DELIVERY_FILES);assert retirebytes==29439574 and deliverybytes==29564682
closed={n:sha(R/n) for n in protected};closed.update({n:sha(R/n) for n in ['reports/full-coverage/pages27-config-execution-v1.json','reports/full-coverage/pages27-config-execution-v1.log','reports/full-coverage/pages27-config-helper3-prewrite-failure-finding-v1.json','reports/full-coverage/approved-inventory55-exact-byte-restoration28-v1.json','reports/full-coverage/approved-inventory55-exact-byte-restoration28-execution-v1.json']})
for n in m.RETIRED_OLD_DELIVERY_FILES:closed[n]=sha(R/n)
out={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':N,'sha256':sha(P)},'helper_sha256':sha(P),'original_review4':{'file':PREV,'sha256':sha(R/PREV)},'entire_original_review4_body_and_time':previous,'entire_helper4_restored_by_exact_reviewed_ast_delta':True,'fresh_fixtures':fixtures,'fresh_fixture_count':len(fixtures),'reused_original_full_code_fixture_count':39,'reused_exclusion_before_symlink_fixture_count':10,'real_native_readonly_prepare_passed':True,'native_prepare_report_preview':report,'prospective_website_bytes_including_native_records':report['prospective_included_website_bytes_including_native_records'],'remaining_prewrite_margin_bytes':850000000-report['prospective_included_website_bytes_including_native_records'],'independent_included_existing_bytes':count,'retired25_exact_file_count':1165,'retired25_exact_bytes':retirebytes,'retired20_23_delivery_exact_bytes':deliverybytes,'required_literal_exclusions':129,'selected_sources':1175,'public_theorems':9644,'required_downloads':1284,'closed_evidence_sha256':closed,'actual_producer_execution_claimed':False,'fixture_directory':str(base),'scope':'Full independent helper5 code and exact helper4 reverse delta; actual retired files Root/PUB/tracked Git HEAD and real completed27/native prepare verified. Isolated guard fixtures have synthetic paths and mock tracked-set only for directory tests; actual full prepare tests all1165 real files with original Git guards. No producer/native output/config writes; original failures/bodies/times held.'};OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'result':str(OUT),'sha256':sha(OUT),'fresh_fixtures':len(fixtures),'website_bytes':out['prospective_website_bytes_including_native_records'],'margin_bytes':out['remaining_prewrite_margin_bytes']}))
