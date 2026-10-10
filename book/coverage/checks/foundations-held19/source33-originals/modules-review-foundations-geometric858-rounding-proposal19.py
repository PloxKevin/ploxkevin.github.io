from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,shutil,sys,importlib.util
R=Path('/home/oxrexkevin/SafetyBased')
def p(x):return Path(x) if Path(x).is_absolute() else R/x
def h(x):return hashlib.sha256(p(x).read_bytes()).hexdigest()
m='/tmp/foundations-geometric-example-rounding-proposal19.json';d=json.loads(p(m).read_text());assert h(m)=='08e2e43ed5e42add07e6576d0c75aa4e5ebe313a8246e62e3faee48366103d0b'
s=d['source'];old=p(s).read_bytes();assert h(s)==d['source_sha256_before'];new=old
for rep in d['replacements']:
 a,b=rep['before'].encode(),rep['after'].encode();assert new.count(a)==rep['count']==1;new=new.replace(a,b,1)
assert hashlib.sha256(new).hexdigest()==d['proposed_source_sha256_after']
rev=new
for rep in reversed(d['replacements']):rev=rev.replace(rep['after'].encode(),rep['before'].encode(),1)
assert rev==old and old.count(b'\n')==new.count(b'\n')
for x,k in [(d['source_bytes_before_snapshot'],'source_sha256_before'),(d['source_bytes_proposed_after_snapshot'],'proposed_source_sha256_after')]:assert h(x)==d[k]
for src,v in d['actual_proof_source_sha256'].items():assert h(src)==v
for e in d['actual_standalone_evidence']:
 assert h(e['compiler_manifest'])==e['compiler_manifest_sha256'];r=json.loads(p(e['compiler_manifest']).read_text());assert r==e['raw_execution_record'];assert r['exit_code']==0 and r['source_unchanged'];assert h(r['source'])==r['source_sha256_before']==r['source_sha256_after'];assert h(r['log'])==r['log_sha256'];assert h(r['preserved_source'])==r['preserved_source_sha256']
sys.path.insert(0,str(R/'book'));from validate import Document
A,B=Document(old.decode()),Document(new.decode());assert len(A.nodes)==len(B.nodes);assert all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(A.nodes,B.nodes))
sim=Path('/tmp/modules-independent-geometric858-rounding19-simulation');assert not sim.exists();(sim/'SafeLearning').mkdir(parents=True)
for f in (R/'SafeLearning').glob('*.html'):shutil.copyfile(f,sim/'SafeLearning'/f.name)
(sim/s).write_bytes(new)
spec=importlib.util.spec_from_file_location('independent_geometric858_inventory19',R/'book/inventory_claims.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v);v.ROOT=sim;v.OUT=sim/'book/coverage';v.inventory()
a=json.loads(p(d['inventory_at_preparation']).read_text());np=v.OUT/'inventory.json';b=json.loads(np.read_text());assert h(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation'];assert a['counts']==b['counts'];delta={}
for typ in ['exercises','material_source_units']:
 aa={x['key']:x for x in a[typ]};bb={x['key']:x for x in b[typ]};assert aa.keys()==bb.keys();delta[typ]=[]
 for k,x in aa.items():
  y=bb[k];assert x.keys()==y.keys()
  for f in x:
   if f not in ['source_sha256','source_text','text_sha256']:assert x[f]==y[f],(k,f)
  if x['source_text']!=y['source_text']:delta[typ].append(k)
  else:assert x['text_sha256']==y['text_sha256']
  if x['source']!=s:assert x==y
assert delta=={'exercises':[],'material_source_units':['primer-basics.html::node-858']}
cm='reports/full-coverage/checkpoint-18-manifest.json';c=json.loads(p(cm).read_text());paths={}
for f,row in c['proof_files'].items():
 paths[f]=row['sha256'];assert h(f)==row['sha256']
 for f,z in row['evidence_sha256'].items():paths[f]=z;assert h(f)==z
for f,z in c['frozen_inputs_sha256'].items():assert h(str(Path(c['snapshot'])/f))==z
assert len(c['proof_files'])==490 and len(paths)==565 and len(c['frozen_inputs_sha256'])==2431
old_review='/tmp/foundations-geometric858-source-components-review19-v1.json';assert h(old_review)=='699745d3664f548f3fa843cddb7941a6d285ecb4be644d1058026a5320acf1fb'
evidence='/tmp/modules-geometric858-explorer-actual19-v2.json';assert p(evidence).exists()
z=dict(schema_version=1,status='approved_narrow_read_only_proposal',reviewer='/root/modules_resume',reviewed_at_utc=datetime.now(timezone.utc).isoformat(),proposal=m,proposal_sha256=h(m),original_proposal_preparation_time_preserved=d['prepared_at_utc'],source=s,source_sha256_before=h(s),proposed_source_sha256_after=hashlib.sha256(new).hexdigest(),inventory=d['inventory_at_preparation'],inventory_sha256=d['inventory_sha256_at_preparation'],exact_substitutions=d['replacements'],fresh_independent_full_parser=dict(actual_command=['python3','/tmp/modules-review-foundations-geometric858-rounding-proposal19.py'],exit_code=0,simulated_inventory=str(np),simulated_inventory_sha256=h(np),counts=b['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_other_fields_unchanged=True,exact_forward_reverse_source_bytes=True),proof_source_sha256=d['actual_proof_source_sha256'],actual_standalone_evidence=d['actual_standalone_evidence'],mathematical_review=[dict(clause='Source tenth power, prefix and tail',decision='approved_precision_qualification',reason='Actual source values have strict non-equalities and certified nearest4/3/3-place decimal enclosures. All three finite values are explicitly qualified as approximations without altering exact limit10 or prefix convention.'),dict(clause='Source genuine logarithmic cutoff',decision='approved_precision_qualification',reason='Actual unrounded log ratio lies strictly above43.7 and within its nearest-one-place rounding interval. Exact first/permanent natural cutoff44 and conservative sufficient47 are both unchanged. No rounded number is substituted into a theorem premise.'),dict(clause='Explorer observation',decision='approved_unchanged_checked_implementation_observation',reason='The prior independently read original IIFE and actual Node replay covers all200 supported slider choices times4horizons with exact integer count arithmetic. This sentence is unchanged; no browser or universal safety claim inferred.')],preserved_prior_precise_review=dict(file=old_review,sha256=h(old_review),semantic_decisions_times_and_missing_preserved=True),protected_selection_integrity=dict(manifest=cm,sha256=h(cm),selected_proofs=490,source_evidence_paths=565,frozen_inputs=2431,all_hashes_exact=True),missing_clauses=[],limits=['TMP-only during explicit HOLD33; no live HTML/inventory/coverage/index writes.','Proposal approval is not source application or fresh whole corrected858 approval; root serialization and later actual-source review remain separate.','Genuine source/evidence hashes and original real linter warning preserved. No new Lean/browser execution inferred.'])
out='/tmp/foundations-geometric-example-rounding-independent-modules-proposal-review19.json';assert not p(out).exists();p(out).write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n');assert p(s).read_bytes()==old;assert h(d['inventory_at_preparation'])==d['inventory_sha256_at_preparation'];print(out,h(out))
