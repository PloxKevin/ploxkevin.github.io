"""Independent full/delta read, exact chain fixtures and real read-only static run."""
from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,sys
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();J=lambda p:json.loads(p.read_bytes());ref=lambda p:{'file':str(p),'sha256':H(p)}
HELP=R/'book/validate28_v1.py';OLD=R/'book/validate.py';AUTHOR=Path('/tmp/root_prepare_static_validator28_v1.py')
assert H(HELP)=='02bc4c20b1aeffe5f4f7ede062bff30228fe8516d2ff1ba8054f8095b7b6094d'and H(OLD)=='29617e224d7105c9f504bb1b0373b2c33b92dd9c03a951c88c965ec27c25be86'
start=datetime.now(timezone.utc).isoformat()
values={}
for n in ast.parse(AUTHOR.read_text()).body:
 if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)and n.targets[0].id in ['addition','old','new']:values[n.targets[0].id]=ast.literal_eval(n.value)
reverse=HELP.read_text().replace(values['addition'],'',1).replace(values['new'],values['old'],1).replace("validator='book/validate28_v1.py',","validator='book/validate.py',")
assert reverse==OLD.read_text()
sel=J(R/'reports/full-coverage/checkpoint-27-selection.json');assert len(sel['proof_files'])==1175
inv=R/'book/coverage/inventory.json';assert H(inv)=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
assets=dict(J(R/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256']);assets.update(J(inv)['source_sha256']);assert len(assets)==31
owners={r['destination']:r['candidate']['sha256']for r in J(R/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']};assert len(owners)==5
protected={n:r['sha256']for n,r in sel['proof_files'].items()};protected.update(assets);protected.update(owners)
plan=J(Path('/tmp/root28-current60-canonical-pair-plan-v1.json'))
for row in plan['sources']:protected[row['canonical_source']]=row['original_tmp_source']['sha256']
extra=R/'verification/lean/SafeLearning/CompleteModulesSensorCommissioning28.lean'
if extra.exists():protected[str(extra.relative_to(R))]=H(extra)
closed=[OLD,HELP,AUTHOR,inv,R/'book/coverage/material-corrections.json',R/'reports/full-coverage/checkpoint-27-selection.json',R/'reports/full-coverage/integration28-source60-static-execution-v1.json',R/'reports/full-coverage/integration28-source60-static-execution-v1.log',R/'reports/full-coverage/integration28-source60-static-execution-v2.json',R/'reports/full-coverage/integration28-source60-static-execution-v2.log',R/'reports/full-coverage/integration-28-source60-static-v2.json',R/'reports/full-coverage/correction59-author-fragment-sync28-execution-v2.json',R/'book/coverage/checks/future28-core/correction59-author-fragment-sync-v1.json']
sync=J(closed[-2]);assert type(sync['actual_exit_code'])is int and sync['actual_exit_code']==0;closed.append(R/sync['log']);assert H(closed[-1])==sync['log_sha256']
for p in [*closed,*sorted((R/'book/chapters').glob('*.html'))]:protected[str(p.relative_to(R))if p.is_relative_to(R)else str(p)]=H(p)
def guard():
 for n,h in protected.items():p=Path(n)if Path(n).is_absolute()else R/n;assert H(p)==h,n
guard()
spec=importlib.util.spec_from_file_location('independent_static_validator28',HELP);m=importlib.util.module_from_spec(spec);sys.modules[spec.name]=m;spec.loader.exec_module(m)
f=m.reverse_documented_corrections;digest=m.digest;cases=[]
def correction(before,after,b,a,i):return {'correction_id':i,'before_sha256':digest(before),'after_sha256':digest(after),'before':b,'after':a}
def accept(name,source,rows,result):assert f(source,rows)==result;cases.append({'name':name,'result':'accepted_exact_expected_bytes'})
def reject(name,source,rows):
 try:f(source,rows)
 except (ValueError,KeyError):cases.append({'name':name,'result':'rejected'})
 else:raise AssertionError('Fixture incorrectly accepted: '+name)
accept('empty correction list','unchanged',[],'unchanged')
c1=correction('A','B','A','B',1);c2=correction('B','C','B','C',2)
accept('single exact transition','B',[c1],'A');accept('chained intermediate before absent from original baseline','C',[c1,c2],'A')
legacy=copy.deepcopy(c1);legacy.pop('correction_id');accept('legacy first-nine schema no correction_id','B',[legacy],'A')
for key in ['before_sha256','after_sha256']:
 bad=copy.deepcopy(c1);bad[key]='0'*64;reject('wrong '+key,'B',[bad])
reject('stale current-page bytes','C',[c1]);reject('out-of-order full-page transitions','C',[c2,c1]);reject('missing earliest transition','C',[c2,c1,c1])
bad=copy.deepcopy(c1);bad['after']='Q';reject('absent replacement fragment','B',[bad])
bad=correction('AA','BB','A','B',3);reject('nonunique fragment even with correct full-page hash','BB',[bad])
bad=correction('A','B','X','B',4);reject('replacement reconstructs wrong before full-page hash','B',[bad])
multi={'correction_id':5,'before_sha256':digest('A D'),'after_sha256':digest('B E'),'replacements':[{'before':'A','after':'B'},{'before':'D','after':'E'}]}
accept('exact multiple replacement row','B E',[multi],'A D');bad=copy.deepcopy(multi);bad['replacements'][0]['before']='X';reject('mutated multiple replacement','B E',[bad])
overlap={'correction_id':6,'before_sha256':digest('A'),'after_sha256':digest('C'),'replacements':[{'before':'A','after':'B'},{'before':'B','after':'C'}]}
accept('within-row successive replacements reversed in reverse order','C',[overlap],'A')
bad=copy.deepcopy(overlap);bad['replacements'].reverse();reject('within-row wrong order','C',[bad])
full_before='body\n<!-- BOOK APPLICATION START -->\nA\n<!-- BOOK APPLICATION END -->\n';full_after=full_before.replace('\nA\n','\nB\n')
insert=correction(full_before,full_after,'\nA\n','\nB\n',7);accept('reverse full-page before removing documented insertions',full_after,[insert],full_before);assert m.remove_insertions(f(full_after,[insert]))==m.remove_insertions(full_before)
reject('stripping insertions before full-hash reversal',m.remove_insertions(full_after),[insert])
allrows=J(R/'book/coverage/material-corrections.json')['corrections'];assert len(allrows)==60
native_chains=[]
for page in sorted({r['source']for r in allrows}):
 rows=[r for r in allrows if r['source']==page];current=(R/page).read_text();original=f(current,rows);assert digest(original)==rows[0]['before_sha256'];native_chains.append({'source':page,'correction_count':len(rows),'original_full_page_sha256':digest(original),'current_full_page_sha256':digest(current)})
assert sum(r['correction_count']for r in native_chains)==60
report=m.validate(allow_reviewed_corrections=True);assert report['status']=='PASS'and report['errors']==[];assert report['counts']['html_pages']==29 and report['counts']['all_current_exercises']==556
assert report['mathematical_correction_exceptions']['count']==60
assert report['build_idempotence']['current_root_already_matches_build']is True and report['build_idempotence']['repeated_build_is_byte_idempotent']is True
assert all(p.get('after_reversing_documented_corrections_matches_baseline',p['original_teaching_body_byte_identical'])for p in report['teaching_page_preservation'])
guard()
OUT=Path('/tmp/static-validator28-independent-applied-reader-v1.json');assert not OUT.exists()
d={'status':'passed_independent_full_current60_static_validator28_code_and_actual_read_only_review','errors':[],'review_started_at_utc':start,'review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELP),'original_validator':ref(OLD),'full_source_and_exact_delta_read':True,'delta_reverses_entire_original_code':True,'fixtures':cases,'native_full60_correction_chains':native_chains,'actual_read_only29_validation':report,'protected_proofs':len(sel['proof_files']),'additional_canonical_sources_guarded':len(protected)-len(sel['proof_files'])-31-5-len(closed)-len(list((R/'book/chapters').glob('*.html'))),'protected_current60_assets':31,'protected_owner_ledgers':5,'original_native_static1_failed_keyerror_preserved':ref(R/'reports/full-coverage/integration28-source60-static-execution-v1.json'),'original_native_static2_true_stale_fragment_failure_preserved':ref(R/'reports/full-coverage/integration28-source60-static-execution-v2.json'),'source59_fragment_sync_actual':ref(closed[-3]),'closed_evidence_sha256':{str(p):H(p)for p in closed},'no_live_source_owner_or_historical_report_write':True,'coverage_complete':False}
with OUT.open('x')as file:file.write(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':d['status'],'reader':ref(OUT),'fixture_count':len(cases),'native29status':report['status']}))
