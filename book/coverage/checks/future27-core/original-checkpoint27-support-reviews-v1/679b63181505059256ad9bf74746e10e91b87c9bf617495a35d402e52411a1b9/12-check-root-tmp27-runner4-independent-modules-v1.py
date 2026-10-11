from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');OLD=Path('/tmp/root_tmp_lean27_runner_v3.py');NEW=Path('/tmp/root_tmp_lean27_runner_v4.py');OUT=Path('/tmp/root-tmp27-runner4-independent-modules-review-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(OLD)=='3336a4d2b00252decb7b7b010f62adfdc9d564d78cbc749ee8f1584242e787b0' and sha(NEW)=='6d552c5cd01daff8f31e246e8a4d9757eb31dfdad78b721fabd77bb5ad8a3518'
old=OLD.read_text();new=NEW.read_text();start=new.index('# Eight new canonical sources');end=new.index('runner_before = sha(Path(__file__))',start)
normalized=new[:start]+new[end:];normalized=normalized.replace("'protected_proof_sources': 1175, 'protected_selected26_proof_sources': 1167,\n    'protected_unselected_paired27_canonical_proof_sources': 8,\n    'actual_unselected27_canonical_pair_readiness': ref(PAIRS27_NAME),\n    'unchanged_baseline25_selected_proof_sources': 1156,", "'protected_proof_sources': 1167, 'unchanged_baseline25_selected_proof_sources': 1156,")
assert normalized==old
# Execute the actual unchanged read-only prefix through guard(), stopping before
# the first source snapshot, log, compiler or output write. No producer execution.
tree=ast.parse(new);prefix=[]
for node in tree.body:
 if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='before' for t in node.targets):break
 prefix.append(node)
assert isinstance(prefix[-1],ast.Expr) and isinstance(prefix[-1].value,ast.Call) and prefix[-1].value.func.id=='guard'
source='/tmp/modules-conformal-common-uniform27-draft-v2.lean';unused='/tmp/root-runner4-independent-native-unused-record-v1.json';saved=sys.argv[:];sys.argv=[str(NEW),source,unused];native={'__file__':str(NEW),'__name__':'independent_read_only_prefix'}
try:exec(compile(ast.Module(body=prefix,type_ignores=[]),str(NEW),'exec'),native)
finally:sys.argv=saved
assert len(native['new27'])==8 and len(native['selection']['proof_files'])==1167 and len(native['seen27'])==16
assert len(native['held'])==1175+31+5
assert not Path(unused).exists() and not Path(unused).with_suffix('.log').exists() and not Path(unused).with_name(Path(unused).stem+'-source.lean').exists()
# Isolate exactly the fresh block, retaining the genuine source/record path set;
# dictionary mutation cases are explicit synthetic fixtures, never actual files.
blocknodes=[];active=False
for node in tree.body:
 if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='PAIRS27_NAME' for t in node.targets):active=True
 if active and isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='runner_before' for t in node.targets):break
 if active:blocknodes.append(node)
block=compile(ast.Module(body=blocknodes,type_ignores=[]),'<explicit synthetic paired-guard fixture>','exec');guardnode=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='guard')
ready=copy.deepcopy(native['pairs27']);actual=copy.deepcopy(native['pair27_actual']);records={r['actual_record']['file']:json.loads((ROOT/r['actual_record']['file']).read_text()) for r in ready['actual_paired_records']};basehashes={n:h for n,h in {**native['held'],**native['PINNED']}.items()};basehashes[str(NEW)]=sha(NEW)
fixtures=[]
def fixture(label,mutate,accept=False):
 r=copy.deepcopy(ready);a=copy.deepcopy(actual);rs=copy.deepcopy(records);hs=copy.deepcopy(basehashes);mutate(r,a,rs,hs)
 def mockread(n):return r if n==native['PAIRS27_NAME'] else a if n==native['PAIR27_ACTUAL_NAME'] else rs[n]
 def mocksha(p):
  n=str(p)
  if n.startswith(str(ROOT)+'/'):n=n[len(str(ROOT))+1:]
  return hs[n]
 env={'ROOT':ROOT,'Path':Path,'read':mockread,'sha':mocksha,'selection':native['selection'],'held':{n:h for n,h in native['held'].items() if n not in native['new27']},'PINNED':{},'__file__':str(NEW),'runner_before':sha(NEW)}
 passed=False
 try:
  exec(block,env);exec(compile(ast.Module(body=[guardnode],type_ignores=[]),'<actual guard function>','exec'),env);env['guard']();passed=True
 except (AssertionError,KeyError):pass
 assert passed is accept,(label,passed,accept);fixtures.append({'name':label,'explicit_synthetic_input':True,'expected_accept':accept,'observed_accept':passed})
fixture('exact native schema copied into isolated memory',lambda *x:None,True)
fixture('readiness errors present',lambda r,a,rs,h:r['errors'].append('bad'))
fixture('source count wrong',lambda r,a,rs,h:r.update(source_count=7))
fixture('export count wrong',lambda r,a,rs,h:r.update(public_theorem_count=140))
fixture('actual wrapper boolean exit',lambda r,a,rs,h:a.update(actual_exit_code=False))
fixture('actual wrapper nonzero exit',lambda r,a,rs,h:a.update(actual_exit_code=1))
fixture('actual command changed',lambda r,a,rs,h:a['actual_command'].append('--extra'))
fixture('actual workdir changed',lambda r,a,rs,h:a.update(actual_workdir='/tmp'))
fixture('helper before after drift',lambda r,a,rs,h:a['helper_sha256_after'].update({'book/coverage/check_core_standalone.py':'0'*64}))
fixture('wrapper log drift',lambda r,a,rs,h:h.update({a['log']:'0'*64}))
fixture('pair missing',lambda r,a,rs,h:r['actual_paired_records'].pop())
fixture('pair duplicate',lambda r,a,rs,h:r['actual_paired_records'].__setitem__(1,copy.deepcopy(r['actual_paired_records'][0])))
fixture('kind unsupported',lambda r,a,rs,h:r['actual_paired_records'][0].update(kind='aggregate'))
fixture('pair boolean exit',lambda r,a,rs,h:r['actual_paired_records'][0].update(actual_exit_code=False))
fixture('canonical record boolean exit',lambda r,a,rs,h:rs[r['actual_paired_records'][0]['actual_record']['file']].update(exit_code=False))
fixture('canonical record command mismatch',lambda r,a,rs,h:rs[r['actual_paired_records'][0]['actual_record']['file']]['command'].append('--extra'))
fixture('canonical record workdir mismatch',lambda r,a,rs,h:rs[r['actual_paired_records'][0]['actual_record']['file']].update(actual_workdir='/tmp'))
fixture('canonical source hash mismatch',lambda r,a,rs,h:rs[r['actual_paired_records'][0]['actual_record']['file']].update(source_sha256_after='0'*64))
fixture('snapshot hash mismatch',lambda r,a,rs,h:r['actual_paired_records'][0]['source_snapshot'].update(sha256='0'*64))
fixture('record byte digest drift',lambda r,a,rs,h:h.update({r['actual_paired_records'][0]['actual_record']['file']:'0'*64}))
fixture('raw log digest drift',lambda r,a,rs,h:h.update({r['actual_paired_records'][0]['raw_log']['file']:'0'*64}))
fixture('snapshot byte digest drift',lambda r,a,rs,h:h.update({r['actual_paired_records'][0]['source_snapshot']['file']:'0'*64}))
fixture('new unselected source current byte drift',lambda r,a,rs,h:h.update({r['sources'][0]['canonical_source']:'0'*64}))
native['guard']()
closed={str(OLD):sha(OLD),str(NEW):sha(NEW),str(Path(__file__)):sha(Path(__file__)),native['PAIRS27_NAME']:native['PAIRS27_SHA'],native['PAIR27_ACTUAL_NAME']:native['PAIR27_ACTUAL_SHA']}
closed.update({n:h for n,h in native['PINNED'].items() if n.startswith('book/coverage/checks/Complete') or 'eight-source141' in n})
with OUT.open('x') as f:f.write(json.dumps({'status':'passed_independent_full_and_exact_delta_current55_tmp_runner4_code_native_guard_and23_fixture_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(NEW),'sha256':sha(NEW)},'helper_sha256':sha(NEW),'original_runner3':{'file':str(OLD),'sha256':sha(OLD)},'exact_reverse_normalization_restores_entire_runner3_bytes':True,'original_compiler_write_execution_flow_exact':True,'actual_read_only_prefix_guard_passed':True,'protected_selected26_sources':1167,'protected_unselected_paired27_sources':8,'protected_proof_sources':1175,'protected_current55_assets':31,'protected_installed26_owner_count':5,'actual_paired_records_read':16,'fixtures':fixtures,'closed_evidence_sha256':closed,'scope':'Independent whole-code read and actual read-only native guard;23 explicitly synthetic paired-schema rejection/acceptance fixtures. No compiler trial or owner/canonical/source write or new aggregate coverage claim.'},indent=2)+'\n')
print(json.dumps({'peer':str(OUT),'sha256':sha(OUT),'status':'passed','fixtures':len(fixtures)}))
