from pathlib import Path
import json,hashlib,datetime,sys,shutil,importlib.util,contextlib,io
R=Path('/home/oxrexkevin/SafetyBased'); sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest(); dig=lambda b:hashlib.sha256(b).hexdigest()
pp=Path('/tmp/modules-design-truncation-precision19-proposal.json');assert sha(pp)=='6f584c34aae450616ee48d67fa4c70c6a7b31b3ba6db09d7f7d8fc5d89852b37';q=json.loads(pp.read_text())
sys.path.insert(0,str(R/'book'));from validate import Document
sp=R/q['source'];raw=sp.read_bytes();assert sha(sp)==q['source_sha256_before'];after=raw.decode()
for z in q['replacements']:
 assert z['count']==1 and after.count(z['before'])==1
 after=after.replace(z['before'],z['after'])
assert dig(after.encode())==q['proposed_source_sha256_after']
reverse=after
for z in reversed(q['replacements']):
 assert reverse.count(z['after'])==1
 reverse=reverse.replace(z['after'],z['before'])
assert reverse.encode()==raw
assert raw.decode().count('\n')==after.count('\n')
a=Document(raw.decode());b=Document(after)
assert [(x.tag,x.attrs,x.line) for x in a.nodes]==[(x.tag,x.attrs,x.line) for x in b.nodes]
for k in ['source_bytes_before_snapshot','source_bytes_proposed_after_snapshot']:
 assert sha(q[k])==q[k+'_sha256']
assert Path(q['source_bytes_before_snapshot']).read_bytes()==raw and Path(q['source_bytes_proposed_after_snapshot']).read_bytes()==after.encode()
ip=R/q['inventory_at_preparation'];assert sha(ip)==q['inventory_sha256_at_preparation'];iv=json.loads(ip.read_text())
base=Path('/tmp/applied-hard3-independent-proposal19-parser');assert not base.exists();(base/'SafeLearning').mkdir(parents=True)
for p in (R/'SafeLearning').glob('*.html'):shutil.copyfile(p,base/'SafeLearning'/p.name)
(base/q['source']).write_bytes(after.encode())
spec=importlib.util.spec_from_file_location('hard3_independent_inventory',R/'book/inventory_claims.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);mod.ROOT=base;mod.OUT=base/'book/coverage';stdout=io.StringIO()
with contextlib.redirect_stdout(stdout):mod.inventory()
np=base/'book/coverage/inventory.json';nv=json.loads(np.read_text());changed={}
for kind in ['exercises','material_source_units']:
 assert len(iv[kind])==len(nv[kind]);changed[kind]=[]
 for x,y in zip(iv[kind],nv[kind]):
  assert x['key']==y['key'];xx=dict(x);yy=dict(y)
  if x['source']==q['source']:
   assert xx.pop('source_sha256')==sha(sp);assert yy.pop('source_sha256')==dig(after.encode())
  if x['source_text']!=y['source_text']:
   changed[kind].append(x['key'])
   for zz in [xx,yy]:zz.pop('source_text');zz.pop('text_sha256')
  assert xx==yy,(kind,x['key'])
assert changed=={'exercises':['lipschitz-by-design.html#practice-hard-3'],'material_source_units':['lipschitz-by-design.html::node-1293']}
ev=[]
for e in q['actual_standalone_evidence']:
 p=R/e['compiler_manifest'];assert sha(p)==e['compiler_manifest_sha256'];j=json.loads(p.read_text());assert j['files']==[e['raw_execution_record']]
 rec=j['files'][0];assert rec['exit_code']==0 and rec['sha256']==sha(R/rec['file']) and sha(R/rec['log'])==rec['log_sha256'];ev.append(e)
for p,h in q['actual_proof_source_sha256'].items():assert sha(R/p)==h
rp=Path('/tmp/modules-design-hard3-truncation-source-components-review19-v1.json');assert sha(rp)=='335249d29d73b52ba7b80de3c440d21e8825a2757e2eaf60060c5cde35e42ba1'
mp=R/'reports/full-coverage/checkpoint-18-manifest.json';m=json.loads(mp.read_text());paths={}
for p,z in m['proof_files'].items():
 assert sha(R/p)==z['sha256'];paths[p]=z['sha256']
 for ep,h in z['evidence_sha256'].items():assert sha(R/ep)==h;paths[ep]=h
for p,h in m['frozen_inputs_sha256'].items():assert sha(R/m['snapshot']/p)==h
assert len(m['proof_files'])==490 and len(paths)==565 and len(m['frozen_inputs_sha256'])==2431
d=dict(schema_version=1,status='independently_approved_read_only_precision_proposal',reviewer='/root/applied_next',reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),proposal=str(pp),proposal_sha256=sha(pp),semantic_source_review=str(rp),semantic_source_review_sha256=sha(rp),source=q['source'],source_sha256_before=sha(sp),proposed_source_sha256_after=dig(after.encode()),inventory=str(ip.relative_to(R)),inventory_sha256=sha(ip),exact_replacements=q['replacements'],actual_standalone_evidence=ev,semantic_decision='Both full actual-zero sources and the entire original question/hint/worked answer were independently read. True matrix exponential orthogonality and certified trigonometric remainders prove the exact rational bound1/750; the new theorem proves strict decimal nonequality and nearest-eight rounding. The correction preserves the exact triangle-derived layer bound1+1/750 and correctly justifies the slightly smaller rounded layer bound by the actual exact norm sqrt1.0004. No change to the algorithm, depth calculation, actual matrix or activation scope is introduced.',actual_full_temporary_parser=dict(exit_code=0,helper='/tmp/review-modules-hard3-precision-proposal19.py',generator='book/inventory_claims.py',generator_sha256=sha(R/'book/inventory_claims.py'),temporary_inventory=str(np),temporary_inventory_sha256=sha(np),stdout=stdout.getvalue(),exercise_count=len(nv['exercises']),material_unit_count=len(nv['material_source_units']),changed_text_keys=changed,all_keys_locators_lines_order_tags_attributes_other_fields_exact=True,all_other_texts_exact=True,forward_reverse_and_DOM_exact=True),protected_bytes=dict(manifest=str(mp.relative_to(R)),manifest_sha256=sha(mp),selected_proofs=490,selected_source_evidence_paths=565,frozen18_inputs=2431,all_exact=True),missing_clauses=[],limits=['TMP-only under HOLD33; no assigned correction index, live HTML/globalinventory write, metadata promotion or root serialization authorization inferred.','Historical source/component review, actual-zero proof/compiler/raw-log bytes and failed trial records remain immutable. Fresh whole corrected-source review is separate after eventual serialized application.'])
op=Path('/tmp/modules-design-hard3-precision-independent-applied-proposal-review19.json');assert not op.exists();op.write_text(json.dumps(d,indent=2)+'\n')
assert sha(sp)==q['source_sha256_before'] and sha(ip)==q['inventory_sha256_at_preparation'];print(op);print(sha(op));print(changed)
