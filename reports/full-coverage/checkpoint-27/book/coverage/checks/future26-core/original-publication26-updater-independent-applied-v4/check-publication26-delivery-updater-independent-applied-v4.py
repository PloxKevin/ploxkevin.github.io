from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,subprocess
R=Path('/home/oxrexkevin/SafetyBased');NAME='book/coverage/checks/root_update_publication26_delivery_progress_v4.py';P=R/NAME
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();EXPECTED='5e83c67bcf7c1db046cde691de0137e7fd9a30f0254afbd7ec9282db59e21a78'
assert H(P)==EXPECTED;body4=P.read_text();nodes4=ast.parse(body4).body
oldpeerpath=R/'book/coverage/checks/future26-core/publication26-delivery-updater-independent-applied-review-v1.json';oldpeer=json.loads(oldpeerpath.read_text());oldpeerhash=H(oldpeerpath)
obspath=Path('/tmp/publication26-delivery-updater-v3-independent-applied-requires-changes-observation-v1.json');obs=json.loads(obspath.read_text());obshash=H(obspath)
assert obs['helper_sha256']=='e2c94e169d4b5ffc105b725c488f30c5dcb10ec50397636994a711f0cad57784';assert obs['whole_prior_v1_peer']==oldpeer
for original,ref in oldpeer['original_closed_byte_aliases'].items():assert H(original)==H(R/ref['file'])==ref['sha256']
# Repeat the exact 28 previously measured isolated guards against this NEW helper.
oldchecker=Path('/tmp/check-publication26-delivery-updater-independent-applied-v2.py');assert H(oldchecker)=='e03682cd90d60ce1daec2421ef74c0845ee8029e2bb5bca308bee93dc4c9d04a'
oldcore=oldchecker.read_text().split("out=Path('/tmp/publication26-delivery-updater-independent-applied-review-v1.json')",1)[0]
core=oldcore.replace('root_update_publication26_delivery_progress_v1.py','root_update_publication26_delivery_progress_v4.py').replace('35465697714e898b2f2fcc692b8f23ae4f0eae7c0365ec12991e9c016ec44a31',EXPECTED)
g={};exec(compile(core,'isolated-original28-fixtures-against-updater4','exec'),g,g);fixtures=g['fixtures'];assert len(fixtures)==28
# Exact narrow delta: only the failed alias/native first-attempt guards and retry2 command.
v3=(R/'book/coverage/checks/root_update_publication26_delivery_progress_v3.py').read_text();assert H(R/'book/coverage/checks/root_update_publication26_delivery_progress_v3.py')==obs['helper_sha256']
retry="assert records['live26-attempt2-execution-v1']['actual_command']==['python3','book/coverage/verify_live19.py','26',commit,'--attempt','2']\n"
newcodes="failed_codes=[failed[k] for k in ('actual_exit_code','exit_code') if k in failed]\nassert failed_codes and all(type(code) is int and code==1 for code in failed_codes)\n"
oldcodes="assert type(failed['actual_exit_code']) is int and failed['actual_exit_code']==1\n"
newrows="""assert len(first_live['assets'])==31 and len({row['source'] for row in first_live['assets']})==31
assert {row['source']:row['expected_sha256'] for row in first_live['assets']}==assets
assert all(type(row['matches']) is bool for row in first_live['assets'])
assert sum(row['matches'] is True for row in first_live['assets'])==24
assert sum(row['matches'] is False for row in first_live['assets'])==7
for row in first_live['assets']:
    if row['matches'] is True:
        assert type(row['http_status']) is int and row['http_status']==200
        assert row['actual_sha256']==row['expected_sha256']==assets[row['source']]
    else:
        assert 'Temporary failure in name resolution' in row.get('error','')
        assert 'actual_sha256' not in row and 'http_status' not in row
"""
oldrows="""assert len(first_live['assets'])==31 and sum(row['matches'] for row in first_live['assets'])==24
assert all('Temporary failure in name resolution' in row.get('error','') for row in first_live['assets'] if not row['matches'])
"""
assert body4.count(retry)==body4.count(newcodes)==body4.count(newrows)==1
assert body4.replace(retry,'').replace(newcodes,oldcodes).replace(newrows,oldrows)==v3
reports=R/'reports/full-coverage';manifest=json.loads((reports/'checkpoint-26-manifest.json').read_text());assets={n:h for n,h in manifest['frozen_inputs_sha256'].items()if n.startswith('SafeLearning/')}
failed=json.loads((reports/'live26-attempt1-execution-v1.json').read_text());first=json.loads((reports/'live-checkpoint-26-attempt1.json').read_text());commit=first['commit']
start=next(i for i,n in enumerate(nodes4)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='failed_name'for t in n.targets));end=next(i for i,n in enumerate(nodes4)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='progress_path'for t in n.targets))
failedcode=compile(ast.Module(body=nodes4[start:end],type_ignores=[]),'isolated-failed-attempt1-native-gates-updater4','exec')
def native_test(label,mutate,want):
 f=copy.deepcopy(failed);l=copy.deepcopy(first);mutate(f,l)
 scope={'REPORTS':reports,'commit':commit,'assets':assets,'read':lambda p:copy.deepcopy(f if p.name=='live26-attempt1-execution-v1.json'else l),'safe':lambda p:R/p,'sha':H}
 accepted=True
 try:exec(failedcode,scope,scope)
 except (AssertionError,KeyError,ValueError,TypeError):accepted=False
 assert accepted==want,(label,accepted,want)
 fixtures.append({'fixture':'new failed/native '+label,'accepted':accepted,'expected_acceptance':want,'synthetic_isolated_native_copy':True})
matched=next(i for i,r in enumerate(first['assets'])if r['matches']is True);dns=next(i for i,r in enumerate(first['assets'])if r['matches']is False)
for label,fn,want in [
 ('actual native31 with24 HTTP matches and7 DNS failures',lambda f,l:None,True),
 ('both strict int1 failure aliases',lambda f,l:f.update(exit_code=1),True),
 ('boolean True failure code',lambda f,l:f.update(actual_exit_code=True),False),
 ('conflicting extra success alias',lambda f,l:f.update(exit_code=0),False),
 ('boolean extra failure alias',lambda f,l:f.update(exit_code=True),False),
 ('all exit aliases missing',lambda f,l:f.pop('actual_exit_code'),False),
 ('failure code2',lambda f,l:f.update(actual_exit_code=2),False),
 ('wrong raw log digest',lambda f,l:f.update(log_sha256='b'*64),False),
 ('wrong failed command attempt',lambda f,l:f['actual_command'].__setitem__(-1,'2'),False),
 ('wrong failed command commit',lambda f,l:f['actual_command'].__setitem__(3,'other'),False),
 ('wrong native first commit',lambda f,l:l.update(commit='other'),False),
 ('wrong native first status',lambda f,l:l.update(status='passed_all31_asset_sha256'),False),
 ('duplicate first source',lambda f,l:l['assets'][-1].update(source=l['assets'][0]['source']),False),
 ('unknown first source',lambda f,l:l['assets'][matched].update(source='SafeLearning/other.html'),False),
 ('wrong first expected digest',lambda f,l:l['assets'][matched].update(expected_sha256='b'*64),False),
 ('wrong matched actual digest',lambda f,l:l['assets'][matched].update(actual_sha256='b'*64),False),
 ('wrong matched HTTP404',lambda f,l:l['assets'][matched].update(http_status=404),False),
 ('matched floating HTTP200',lambda f,l:l['assets'][matched].update(http_status=200.0),False),
 ('integer1 matches instead of boolTrue',lambda f,l:l['assets'][matched].update(matches=1),False),
 ('integer0 matches instead of boolFalse',lambda f,l:l['assets'][dns].update(matches=0),False),
 ('wrong DNS reason',lambda f,l:l['assets'][dns].update(error='HTTP 404'),False),
 ('DNS row carries actual body digest',lambda f,l:l['assets'][dns].update(actual_sha256=l['assets'][dns]['expected_sha256']),False),
 ('DNS row carries HTTP status',lambda f,l:l['assets'][dns].update(http_status=200),False),
 ('missing first source row',lambda f,l:l['assets'].pop(),False),
 ('changed24/7 count',lambda f,l:l['assets'][matched].update(matches=False,error='Temporary failure in name resolution'),False)
]:native_test(label,fn,want)
retryassert=next(n for n in nodes4 if isinstance(n,ast.Assert)and ast.unparse(n).startswith("assert records['live26-attempt2-execution-v1']['actual_command']"))
retry2=json.loads((reports/'live26-attempt2-execution-v1.json').read_text())
for label,fn,want in [('actual successful attempt2 command',lambda d:None,True),('success wrapper points at attempt1',lambda d:d['actual_command'].__setitem__(-1,'1'),False),('success wrapper wrong commit',lambda d:d['actual_command'].__setitem__(3,'other'),False),('success wrapper wrong program',lambda d:d['actual_command'].__setitem__(1,'other.py'),False)]:
 d=copy.deepcopy(retry2);fn(d);ok=True
 try:exec(compile(ast.Module(body=[retryassert],type_ignores=[]),label,'exec'),{'records':{'live26-attempt2-execution-v1':d},'commit':commit})
 except (AssertionError,KeyError):ok=False
 assert ok==want,label;fixtures.append({'fixture':'new retry2 '+label,'accepted':ok,'expected_acceptance':want,'synthetic_isolated_native_copy':True})
# Execute the complete real prewrite guard prefix only, excluding all backup/write calls.
writeboundary=next(i for i,n in enumerate(nodes4)if isinstance(n,ast.For)and 'zip([progress_path, readme_path], backup_names)'in ast.unparse(n))
prefix=nodes4[:writeboundary]
for n in prefix:
 for c in ast.walk(n):
  if isinstance(c,ast.Call)and isinstance(c.func,ast.Attribute):assert c.func.attr not in {'write_text','write_bytes','copyfile','mkdir','open'},ast.unparse(c)
protected=[P,R/'book/coverage/progress.json',reports/'README.md',oldpeerpath,obspath,R/'book/coverage/inventory.json',R/'book/coverage/inventory-after-correction53.json',R/'book/coverage/material-corrections.json']
protected.extend(R/n for n in assets)
protected.extend(R/ref['file']for ref in oldpeer['original_closed_byte_aliases'].values())
protected.extend(R/'book/coverage'/n for n in ['core.json','foundations.json','applied.json','modules.json','applied-exercise-promotions.json'])
protected=[p for p in protected if p.is_file()];beforehashes={str(p):H(p)for p in protected}
real={'__file__':str(P)};exec(compile(ast.Module(body=prefix,type_ignores=[]),'full-real-read-only-prewrite-prefix-updater4','exec'),real,real)
assert all(H(p)==h for p,h in beforehashes.items());assert not (reports/'progress-checkpoint26-delivery-update-v1.json').exists()
fixtures.append({'fixture':'all real native guards before backups accept actual31 successful retry and preserved24/7 DNS failure','accepted':True,'synthetic_only':False,'scope':'Read-only prewrite prefix only; excluded every copy/write/output statement.'})
assert body4.index("failed_name='live26-attempt1-execution-v1.json'")<body4.index('shutil.copyfile(source,target)')<body4.index('progress_path.write_text')
assert H(P)==EXPECTED and H(oldpeerpath)==oldpeerhash and H(obspath)==obshash
native_names=['live-checkpoint-26-attempt1.json','pages-checkpoint-26-attempt1.json','pages-checkpoint-26-attempt1.log','live26-attempt1-execution-v1.json','live26-attempt1-execution-v1.log','live-checkpoint-26-attempt2.json','pages-checkpoint-26-attempt2.json','pages-checkpoint-26-attempt2.log']
for stem in real['stems']:native_names.extend([stem+'.json',stem+'.log'])
native={str((reports/n).relative_to(R)):H(reports/n)for n in native_names}
out=Path('/tmp/publication26-delivery-updater-independent-applied-review-v4.json');assert not out.exists()
out.write_text(json.dumps({'status':'passed_independent_full_code_and_isolated_native_guard_fixture_review','errors':[],'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':NAME,'sha256':EXPECTED},'helper_sha256':EXPECTED,'entire_reviewed_helper_body':body4,'full_code_read':True,'exact_v4_delta_reverses_to_held_v3':True,'fixtures':fixtures,'fixture_count':len(fixtures),'whole_prior_v1_peer_body_and_time':oldpeer,'whole_v3_requires_changes_observation_body_and_time':obs,'preserved_v3_observation':{'file':str(obspath),'sha256':obshash},'native_read_only_guard_inputs_sha256':native,'protected_read_only_file_count':len(beforehashes),'protected_read_only_sha256_before_after':beforehashes,'actual_scope':'Full unexecuted updater4 code and isolated guard fixtures, plus its complete real READ-ONLY prewrite prefix only. No backup/progress/README/output/PUB/Git/owner write, no updater producer execution or delivery-update result. Actual successful retry2 and unchanged genuine failed1 inspected; all historical original review bodies/times/failures remain exact.','native_schema_notes':['Every present successful exit alias is strict integer0; failed1 aliases are strict integer1 and exact attempt1 command/raw log.','First31 unique expected hashes equal the actual frozen source map;24 strict True HTTP200 matched-body hashes and7 strict False DNS rows without invented body/HTTP verified before writes.','Successful retry2 exact command pinned; actual live31/source/current ROOT+PUB bytes and actual Pages completed jobs remain required.','Exact metadata inverse preserves the entire checkpoint25 history, proof/semantic/review fields and partial coverage.','Previous28 fixtures repeated transparently against updater4; original reader1 failure/reader2 pass and v3 diagnostic completion remain unchanged.']},indent=2)+'\n')
print(json.dumps({'peer':str(out),'sha256':H(out),'fixtures':len(fixtures),'native_read_only_inputs':len(native),'protected_files':len(beforehashes)}))
