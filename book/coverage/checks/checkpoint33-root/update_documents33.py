"""Record the completed local checkpoint33 while preserving original documents."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, shutil
ROOT = Path(__file__).resolve().parents[4]
HISTORY = 'reports/full-coverage/source-history/documentation32-before-checkpoint33-v1'
def read(n): return json.loads((ROOT/n).read_bytes())
def sha(n): return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def ref(n): return dict(file=n,sha256=sha(n))
def write(n,d): (ROOT/n).write_text(json.dumps(d,indent=2)+'\n')
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--visual-review',required=True)
ap.add_argument('--visual-review-sha256',required=True)
args=ap.parse_args()
assert sha(args.visual_review)==args.visual_review_sha256
visual=read(args.visual_review)
assert visual['status'].startswith('passed')
manifest=read('reports/full-coverage/checkpoint-33-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage'
audit=read(manifest['successful_verification']['report'])
assert audit['status']=='passed' and audit['proof_file_count']==1261 and audit['theorem_count']==11345
ledger=read('reports/full-coverage/ledger33-working-v1.json')
assert ledger['integrity_status']=='passed' and ledger['counts']['material_review_statuses']=={'reviewed':4851,'pending':7923}
browser='reports/full-coverage/browser33-source88-learning-v1.json'
assert len(read(browser))==2 and all(r['status']=='passed' and r['errors']==[] for r in read(browser))
regions='reports/full-coverage/browser33-source88-changed-regions-v1.json'
assert read(regions)['status']=='passed' and read(regions)['source_bytes_preserved'] is True
assert all(r['source_sha256']==audit['source_sha256']['SafeLearning/'+r['file']] for r in read(browser))
assert not (ROOT/HISTORY).exists()
names=['README.md','book/README.md','verification/lean/README.md','reports/full-coverage/README.md','book/coverage/progress.json','book/coverage/CONTINUATION.md','_config.yml']
originals={}
for n in names:
 p=ROOT/HISTORY/n;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/n,p);originals[n]=ref(p.relative_to(ROOT).as_posix())
p=read('book/coverage/progress.json')
assert p['verified_checkpoint']['checkpoint']==32
p['previous_checkpoint32_delivery']=dict(entire_original_progress=originals['book/coverage/progress.json'],content_commit=p['last_published_content_commit'],metadata_commit=p['last_published_metadata_commit'],actual_delivery_closure=p['live_delivery_evidence']['actual_delivery_closure'])
p['inventory_sha256']=manifest['inventory_sha256']
p['current_documented_material_corrections']=88
p['verified_checkpoint']=dict(checkpoint=33,proof_files=1261,theorems=11345,status='passed',coverage_complete=False,report=manifest['successful_verification']['report'],actual_audit_workdir=manifest['successful_verification']['actual_workdir'],actual_execution=ref('reports/full-coverage/verify-runtime33-execution-v1.json'),fresh_kernel_files=7,exact_prior_kernel_reuses=1254)
p['working_coverage_report']='reports/full-coverage/ledger33-working-v1.json'
p['current_published_ledger_candidate']='reports/full-coverage/ledger33-frozen-source-only-v1.json'
p['current_frozen_audit']=dict(snapshot=manifest['snapshot'],source_only=True,proof_files=1261,status='source_exact_mirror_of_actual_runtime_audit',snapshot_execution_claimed=False,manifest=ref('reports/full-coverage/checkpoint-33-manifest.json'))
p['publication_status']='checkpoint33_locally_verified_content_delivery_pending'
p['live_delivery_status']='checkpoint32_delivery_confirmed_checkpoint33_delivery_pending'
p['working_next_checkpoint_preparation']=dict(status='checkpoint33_locally_verified_full_coverage_objective_unfinished',inventory='book/coverage/inventory.json',inventory_sha256=manifest['inventory_sha256'],exercise_counts=dict(complete=536,partial=8,pending=12),material_review_units=dict(reviewed=4851,pending=7923),owner33_integration=ref('reports/full-coverage/owner33-integration-v1.json'),browser=ref(browser),regions=ref(regions),visual_review=ref(args.visual_review),coverage_complete=False)
write('book/coverage/progress.json',p)
remaining=[];owners={}
for domain in ['foundations','applied','modules','core']:
 n='book/coverage/'+domain+'.json';owners[n]=sha(n)
 for e in read(n)['exercises']:
  if e['status']!='complete_math':
   remaining.append(dict(owner=domain,inventory_key=e['inventory_key'],label=e['label'],status=e['status'],pending_claims=[c for c in e['claims'] if c['status']!='proved']))
assert len(remaining)==20
assert not (ROOT/'book/coverage/remaining-exercises33.json').exists()
write('book/coverage/remaining-exercises33.json',dict(generated_at_utc=datetime.now(timezone.utc).isoformat(),checkpoint=33,owner_sha256=owners,exercises=remaining,scope='Current incomplete exercises and their exact unproved claims; historical mathematical and native reviews remain in the owner ledgers.',coverage_complete=False))
for n in ['README.md','book/README.md','verification/lean/README.md']:
 s=(ROOT/n).read_text().replace('11,267','11,345').replace('1,254','1,261').replace('7,933','7,923')
 if n=='README.md':
  s=s.replace('32 is published with all 31 live asset hashes confirmed; it adds six proof\nfiles and six reviewed material mappings.', '33 is verified locally and awaits delivery; it adds seven proof files,\n78 theorems and ten reviewed material mappings.')
 if n=='verification/lean/README.md':
  s=s.replace('Six new modules received fresh kernel replays; 1,248 exact earlier results','Seven new modules received fresh kernel replays; 1,254 exact earlier results').replace('runtime-checkpoint-32-source81-recovery-v1','runtime-checkpoint-33-source88-v1').replace('checkpoint32 runtime','checkpoint33 runtime')
 (ROOT/n).write_text(s)
config=(ROOT/'_config.yml').read_text()
assert config.count('exclude:\n') == 1 and config.rstrip().splitlines()[-1].startswith('  - ')
excluded=['book/coverage/inventory-'+side+'-correction'+str(k)+'.json' for k in range(82,89) for side in ['before','after']]
excluded+=['reports/full-coverage/source33-parsers-v1','reports/full-coverage/source33-parsers-v2']
for n in excluded:
 line='  - '+n+'\n'
 if line not in config: config+=line
(ROOT/'_config.yml').write_text(config)
(ROOT/'reports/full-coverage/README.md').write_text('''# Continuing full mathematical coverage

Checkpoint 33 passed the local Lean 4.34.1 build, kernel checks and standard-axiom
audit: **11,345 public theorems in 1,261 selected files**. Seven new files passed
standalone and named builds and received fresh kernel replays. The 1,254 earlier
kernel results were reused after exact source, transitive import and pinned
dependency identities matched. The aggregate build and every theorem's axiom
audit ran again. The [original audit](lean-checkpoint-33-source88-v1/verification-original.json)
and [actual execution](verify-runtime33-execution-v1.json) preserve commands,
logs, source identities, times and runtime paths. All axiom dependencies are standard.

Coverage remains partial: **536 of 556 exercises are complete, 8 partial and
12 pending**. Of 12,774 overlapping material units, **4,851 are reviewed and
7,923 pending**. The [working ledger](ledger33-working-v1.json) and
[frozen ledger](ledger33-frozen-source-only-v1.json) pass integrity checks.
Independent reviews establish exact source correspondence and assumptions.

The batch adds 78 theorems about local regular-root Newton convergence and rates,
induced matrix norms, box-image zonotopes, cube covers and margin transfer,
signed and Hausdorff distances, subunit power norms, and planar quadratic level sets.
Corrections 82–88 make their required domains precise. The
[source application](checkpoint33-source-corrections82-88-v1.json) and
[independent owner review](../../book/coverage/checks/checkpoint33-review/independent-four-owner-candidates-review-v4.json)
support ten whole material promotions, eighteen component rebases and one bounded
rate component. The broader linked algorithms in Basics node922 and Filippov
integral-curve existence remain pending. Every exercise status is preserved.

[Static checks](integration33-source88-v1.json) pass for 29 pages, 556 exercises
and 21 labs. Fresh [browser checks](browser33-source88-learning-v1.json) cover
both changed pages at five widths, keyboard disclosures, practice, sliders,
math rendering and print. Fresh [region captures](browser33-source88-changed-regions-v1.json)
cover the changed source regions; their visual inspection is recorded separately
in the progress ledger. Current static checks use `book/validate28_v1.py`.
Earlier failed attempts retain their actual outcomes.

The [selection](checkpoint-33-selection.json) retains every checkpoint32 source.
The [manifest](checkpoint-33-manifest.json) identifies a source-only snapshot
without previous snapshots or Lean build trees. The actual compiler ran in
`runtime-checkpoint-33-source88-v1`; the frozen snapshot mirrors its source bytes.
Only three unused Applied proof metadata entries are omitted from the frozen
ledger; every claim remains. The working tree retains unselected historical
proofs. A published checkout uses selected sources at their normal paths.

Checkpoint 33 is verified locally; its GitHub delivery is pending.
Checkpoint32 content and metadata delivery is [fully confirmed](publication32-finish-recovery-v1.json).
Full mathematical coverage remains unfinished. The [continuation note](../../book/coverage/CONTINUATION.md)
and [remaining exercises](../../book/coverage/remaining-exercises33.json) identify further work.

To reproduce the selected snapshot, use fresh report paths:

```sh
cd reports/full-coverage/checkpoint-33
python3 book/coverage/validate.py --output reports/ledger-reproduction33.json
cd verification/lean
lake exe cache get
python3 verify.py --output ../../reports/lean-reproduction33
```

The [published Lean sources](https://github.com/PloxKevin/ploxkevin.github.io/tree/main/verification/lean)
and original evidence remain in Git.
''')
(ROOT/'book/coverage/CONTINUATION.md').write_text('''# Continue full mathematical coverage

The objective remains every exercise and established mathematical teaching
claim, with local Lean proofs, exact source correspondence, independent review
and published evidence. Passing checkpoints represent partial progress.

Checkpoint33 checks 11,345 theorems in 1,261 selected files. Coverage is
536 complete, 8 partial and 12 pending exercises; 4,851 reviewed and 7,923
pending overlapping material units. `remaining-exercises33.json` lists the
20 incomplete exercises and their current unproved subclaims. Read `progress.json`
and `../../reports/full-coverage/README.md` for actual delivery status.

The selected audit ran in `../../reports/full-coverage/runtime-checkpoint-33-source88-v1`.
The source-only `../../reports/full-coverage/checkpoint-33` reproduces its bytes.
Its manifest and selection retain all earlier selected proofs. The main working
Lean tree retains unselected historical sources; its default aggregate differs
from the selected runtime. Use the selected snapshot for reproduction.

The publication Git checkout is `../../reports/book/publication-repo`.
The project root has no Git repository. Preserve original command receipts,
raw logs, owner ledgers and source history. Use fresh outputs for each run.
Copy no earlier snapshot tree or `.lake` output into new snapshots.
Current static checks use `../validate28_v1.py --allow-reviewed-corrections`;
the older validator does not support the chained source-correction registry.

Source88 applies corrections82–88 to Basics and Linalg, with exact inverse and
independent full29-page inventory evidence. The seven families in
`checks/recovery32/next-batch-source-qualification-index-v1.json` are now selected;
do not add or promote them again. Ten whole material units are newly reviewed,
eighteen carried components are rebased, and one Basics node922 component is
proved. Broader linked algorithm obligations in whole node922 remain pending.

The current next-work index is `checks/checkpoint33-review/next-unselected-work-index-v1.json`.
Prepared conditional-expectation and neural-loop packets remain unselected
until their exact correspondence requirements are met. Filippov polygonal
construction is a component: actual integral-curve existence, derivative
inclusion and the enclosing invariance exercise remain open. Inspect exact
packet bytes, statements and peers before changing source or promoting coverage.
''')
write('reports/full-coverage/documentation33-local-verification-v1.json',dict(status='passed_actual_checkpoint33_local_verification_documents_updated_delivery_pending',preserved_originals=originals,manifest=ref('reports/full-coverage/checkpoint-33-manifest.json'),browser=ref(browser),regions=ref(regions),visual_review=ref(args.visual_review),coverage_complete=False))
print(json.dumps(dict(status='passed',checkpoint=33,delivery_pending=True,coverage_complete=False)))
