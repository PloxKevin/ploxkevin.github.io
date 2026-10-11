"""Exact helper AST pre-write checks against adapted native reports; no production writer."""
from pathlib import Path
import ast, copy, hashlib, json, re, tempfile, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
HELPER = ROOT / 'book/coverage/checks/root_prepare_checkpoint27_documentation_v1.py'
helper_bytes = HELPER.read_bytes()
def sha_bytes(b): return hashlib.sha256(b).hexdigest()
def native(n): return json.loads((ROOT/n).read_bytes())
tree = ast.parse(helper_bytes)
start = next(i for i,n in enumerate(tree.body) if isinstance(n, ast.Assign) and any(isinstance(t,ast.Name) and t.id=='auditn' for t in n.targets))
stop = next(i for i,n in enumerate(tree.body) if isinstance(n, ast.For) and isinstance(n.target,ast.Tuple) and any(isinstance(t,ast.Name) and t.id=='body' for t in n.target.elts))
definitions = compile(ast.Module(body=tree.body[:start],type_ignores=[]),str(HELPER),'exec')
prewrite = compile(ast.Module(body=tree.body[start:stop],type_ignores=[]),str(HELPER),'exec')
fixture_root=Path(tempfile.mkdtemp(prefix='documentation27-native-prewrite-v1-'))
(fixture_root/'book/coverage').mkdir(parents=True)
(fixture_root/'reports/full-coverage').mkdir(parents=True)
(fixture_root/'book/coverage/progress.json').write_bytes((ROOT/'book/coverage/progress.json').read_bytes())
(fixture_root/'reports/full-coverage/README.md').write_bytes((ROOT/'reports/full-coverage/README.md').read_bytes())

baseline_selection = native('reports/full-coverage/checkpoint-26-selection.json')
selection = native('reports/full-coverage/checkpoint-27-selection.json')
new = sorted(set(selection['proof_files'])-set(baseline_selection['proof_files']))
assert len(new)==8
audit = native('reports/full-coverage/lean-checkpoint-26/verification-original.json')
audit['proof_file_count']=1175
audit['theorem_count']=9644
audit['proof_sha256']={n:r['sha256'] for n,r in selection['proof_files'].items()}
oldchecks=[]
for c in audit['checks']:
 c=copy.deepcopy(c)
 c['command']=[x.replace('checkpoint-26','checkpoint-27') for x in c['command']]
 if 'evidence_mode' in c:c['evidence_mode']='reused_identical_module_and_transitive_local_imports'
 oldchecks.append(c)
template=copy.deepcopy(next(c for c in audit['checks'] if c.get('evidence_mode')=='fresh_kernel_replay'))
fresh=[]
for n in new:
 text=(ROOT/n).read_text();ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
 names=re.findall(r'^(?:theorem|lemma)\s+(\S+)',text,re.M)
 for name in names:
  name=ns+'.'+name
  audit['declarations'].append({'name':name,'file':n})
  audit['axiom_dependencies'][name]=['propext','Classical.choice','Quot.sound']
 c=copy.deepcopy(template);c['evidence_mode']='fresh_kernel_replay';c['command']=['lake','env','lean',n];fresh.append(c)
audit['checks']=oldchecks[:-1]+fresh+oldchecks[-1:]
assert len(audit['declarations'])==len(audit['axiom_dependencies'])==9644
manifest=native('reports/full-coverage/checkpoint-26-manifest.json')
manifest['snapshot']='reports/full-coverage/checkpoint-27'
manifest['selection']='reports/full-coverage/checkpoint-27-selection.json'
manifest['proof_files']=selection['proof_files']
manifest['selection_sha256']=sha_bytes((ROOT/'reports/full-coverage/checkpoint-27-selection.json').read_bytes())
browser=native('reports/full-coverage/browser-checkpoint-27.json')
manifest['frozen_inputs_sha256'].update(browser['source_sha256'])
ledger=native('reports/full-coverage/lean-checkpoint-26/ledger-audit.json')
ledger['inventory_sha256']=sha_bytes((ROOT/'book/coverage/inventory-after-correction55.json').read_bytes())
ledger['counts']['statuses'].update({'exercise:complete_math':519,'exercise:partial':16,'exercise:pending':21})
ledger['counts']['material_review_statuses']={'reviewed':4574,'pending':8200}
static=native('reports/full-coverage/integration-26.json')
objects={'reports/full-coverage/lean-checkpoint-27/verification-original.json':audit,
 'reports/full-coverage/checkpoint-27-manifest.json':manifest,
 'reports/full-coverage/lean-checkpoint-27/ledger-audit.json':ledger,
 'reports/full-coverage/integration-27.json':static,
 'reports/full-coverage/browser-checkpoint-27.json':browser}
raw={'book/coverage/inventory-after-correction55.json':(ROOT/'book/coverage/inventory-after-correction55.json').read_bytes()}
for stem in ['verify','export','export-integrity','frozen-ledger','static']:
 oldname='reports/full-coverage/'+stem+'-checkpoint26-execution-v1.json'
 newname=oldname.replace('26','27')
 d=native(oldname)
 d['log']=d['log'].replace('26','27'); raw[d['log']]=(ROOT/native(oldname)['log']).read_bytes()
 d['log_sha256']=sha_bytes(raw[d['log']])
 helpers={}
 for n in d['helper_sha256_after']:
  newn=n.replace('26','27');raw[newn]=(ROOT/n).read_bytes();helpers[newn]=sha_bytes(raw[newn])
 d['helper_sha256_before']=dict(helpers);d['helper_sha256_after']=dict(helpers)
 d['actual_command']=[x.replace('26','27') for x in d['actual_command']]
 if stem=='verify':d['actual_command']=['python3','reports/full-coverage/checkpoint-27/verification/lean/verify.py','--reuse-kernel-from',str(fixture_root/'reports/full-coverage/checkpoint-26')]
 objects[newname]=d

def run(label, mutate=None, expect=True):
 # Copy only the object mutated by a fixture; preserve full native objects otherwise.
 vals=dict(objects); raws=dict(raw)
 if mutate: mutate(vals,raws)
 vals['reports/full-coverage/checkpoint-27-manifest.json']=dict(vals['reports/full-coverage/checkpoint-27-manifest.json'])
 m=vals['reports/full-coverage/checkpoint-27-manifest.json']
 m['successful_verification']=dict(m['successful_verification'])
 def digest(n):
  if n in raws:return sha_bytes(raws[n])
  if n in vals:return sha_bytes(json.dumps(vals[n],sort_keys=True,separators=(',',':')).encode())
  return sha_bytes((ROOT/n).read_bytes())
 m['successful_verification']['report_sha256']=digest('reports/full-coverage/lean-checkpoint-27/verification-original.json')
 ns={'__file__':str(HELPER)};exec(definitions,ns)
 ns.update(ROOT=fixture_root,REPORTS=fixture_root/'reports/full-coverage',read=lambda n:vals[n],sha=lambda p:digest(str(p.relative_to(fixture_root))),ref=lambda n:{'file':n,'sha256':digest(n)})
 before=sha_bytes((ROOT/'book/coverage/progress.json').read_bytes())
 started=time.monotonic()
 try:exec(prewrite,ns);accepted=True;error=None
 except Exception as e:accepted=False;error=type(e).__name__+': '+str(e)
 assert sha_bytes((ROOT/'book/coverage/progress.json').read_bytes())==before
 row={'fixture':label,'accepted':accepted,'expected_acceptance':expect,'expectation_met':accepted==expect,'error':error,'elapsed_seconds':round(time.monotonic()-started,6)}
 if accepted and label=='adapted native-schema positive control':
  row['prepared_live_delivery_evidence']=ns['progress']['live_delivery_evidence']
  row['prepared_delivery_status']=ns['progress']['live_delivery_status']
  row['original_progress_archived']=ns['progress']['previous_checkpoint26_delivery']['entire_original_progress']
 print(json.dumps(row));return row

def change_obj(n,fn):
 def mutate(v,r):v[n]=copy.deepcopy(v[n]);fn(v[n])
 return mutate
A='reports/full-coverage/lean-checkpoint-27/verification-original.json'
B='reports/full-coverage/browser-checkpoint-27.json'
E='reports/full-coverage/verify-checkpoint27-execution-v1.json'
results=[]
results.append(run('adapted native-schema positive control'))
results.append(run('mismatched axiom/declaration name',change_obj(A,lambda d:d['declarations'][0].update(name='SafeLearning.UnindexedWrongDeclaration')),False))
results.append(run('duplicate declaration name preserving length',change_obj(A,lambda d:d['declarations'].__setitem__(0,dict(d['declarations'][1]))),False))
results.append(run('wrong Lean version',change_obj(A,lambda d:d.update(lean_version='Lean (version 4.0.0, synthetic wrong environment)')),False))
results.append(run('wrong mathlib revision',change_obj(A,lambda d:d.update(mathlib_revision='0'*40)),False))
results.append(run('changed selected proof digest',change_obj(A,lambda d:d['proof_sha256'].__setitem__(next(iter(d['proof_sha256'])),'0'*64)),False))
results.append(run('browser failed status',change_obj(B,lambda d:d.update(status='failed')),False))
results.append(run('browser manual inspection pending',change_obj(B,lambda d:d['manual_visual_inspection'].update(status='pending',fresh_actual_captures=0,retained_exact_capture_count=0)),False))
results.append(run('browser four-manual-review hash corrupted',change_obj(B,lambda d:d['manual_visual_inspection']['new_original_four_review'].update(sha256='0'*64)),False))
results.append(run('browser QA fingerprints corrupted',change_obj(B,lambda d:d['qa_source_sha256'].__setitem__(next(iter(d['qa_source_sha256'])),'0'*64)),False))
results.append(run('browser viewport total inconsistent',change_obj(B,lambda d:d.update(verified_viewport_count=0)),False))
results.append(run('browser skipped target count inconsistent',change_obj(B,lambda d:d.update(skipped_capture_target_count=99)),False))
results.append(run('unsafe axiom',change_obj(A,lambda d:d['axiom_dependencies'].__setitem__(next(iter(d['axiom_dependencies'])),['sorryAx'])),False))
results.append(run('bool false execution exit',change_obj(E,lambda d:d.update(actual_exit_code=False)),False))
results.append(run('wrong actual execution command',change_obj(E,lambda d:d.update(actual_command=['python3','unexecuted.py'])),False))
results.append(run('changed execution log body',lambda v,r:r.__setitem__(v[E]['log'],b'changed historical log\n'),False))
results.append(run('empty execution helper fingerprints',change_obj(E,lambda d:d.update(helper_sha256_before={},helper_sha256_after={})),False))
report={'status':'requires_changes_independent_full_code_and_native_schema_prewrite_guard_review','approved':False,'helper':{'file':str(HELPER.relative_to(ROOT)),'sha256':sha_bytes(helper_bytes)},'full_code_read':True,'prior26_context_read':True,'fixture_count':len(results),'fixtures':results,'unexpected_acceptance_count':sum(x['accepted'] and not x['expected_acceptance'] for x in results),'source_native_reports':['reports/full-coverage/lean-checkpoint-26/verification-original.json','reports/full-coverage/checkpoint-26-manifest.json','reports/full-coverage/checkpoint-27-selection.json','reports/full-coverage/lean-checkpoint-26/ledger-audit.json','reports/full-coverage/integration-26.json','reports/full-coverage/browser-checkpoint-27.json'],'scope':'Exact full pre-write AST guards and progress/readme calculations; native26 reports adapted to expected27 counts/source names to exercise guard behavior. No actual27 verification inferred, no compiler invocation, no production writer or repository mutations. Positive control is synthetic native-schema adapter, not passing27 evidence.','isolated_fixture_root':str(fixture_root),'errors':['Audit identity/version/selected proof mappings accept altered native evidence','Browser failed/pending manual/hash/QA/count evidence accepts altered native evidence','Actual execution permits empty helper fingerprints','New progress retains previous26 live_delivery_evidence under delivery-pending27 status']}
out=Path('/tmp/documentation27-independent-foundations-native-review-v1.json');out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'review':str(out),'sha256':sha_bytes(out.read_bytes()),'fixture_count':len(results),'unexpected_acceptance_count':report['unexpected_acceptance_count']}))
