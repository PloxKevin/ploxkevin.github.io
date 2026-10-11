"""Stage a literal archive-exclusion repair and unchanged actual checkpoint20 evidence."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,subprocess,time
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo';REPORTS=ROOT/'reports/full-coverage'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
peer=ROOT/'book/coverage/checks/pages20-size-exclusion-independent-foundations-review-v1.json'
review=read(peer)
assert review['config_sha256']==sha(PUB/'_config.yml')=='5240887696b71ede4f92468c459116dcd874de7ba3e870ef300bd4ad1d30ae82'
assert review['status'].startswith('independent') and 'passed' in review['status']
manifest=read(REPORTS/'checkpoint-20-manifest.json');assert manifest['status']=='formal_verification_passed_partial_coverage'
assets={k:v for k,v in manifest['frozen_inputs_sha256'].items() if k.startswith('SafeLearning/')};assert len(assets)==31
for name,digest in assets.items(): assert sha(PUB/name)==digest
names={'_config.yml','book/coverage/progress.json','reports/full-coverage/README.md'}
evidence={'book/coverage/checks/root_stage_pages20_repair_v1.py',str(peer.relative_to(ROOT))}
for basename in ['stage-publication20-wrapper','publication-checkpoint20-staging-execution','publication-checkpoint20-staging-whitelist','publication-checkpoint20-prestage-integrity','publication-extra20-files','publication20-content-delivery-execution','pages20-content-failed-workflow-original','pages20-size-exclusion-preparation-v1','live-checkpoint20-attempt1-execution','live-checkpoint20-attempt2-execution','live-checkpoint-20-attempt1','live-checkpoint-20-attempt2','pages-checkpoint-20-attempt1','pages-checkpoint-20-attempt2']:
 for ext in ['.json','.log']:
  name='reports/full-coverage/'+basename+ext
  if (ROOT/name).exists(): evidence.add(name)
for basename in ['commit','head','push','remote']: evidence.add('reports/full-coverage/publication20-content-'+basename+'.log')
evidence.update(['reports/full-coverage/lean-checkpoint-20/ledger-audit.json','reports/full-coverage/publication-checks/ledger-checkpoint-20.json'])
for name in sorted(evidence):
 source=ROOT/name;target=PUB/name
 assert source.is_file() and not source.is_symlink() and source.stat().st_size<100_000_000
 target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);assert sha(target)==sha(source)
names.update(evidence)
expected={name:sha(PUB/name) for name in sorted(names)}
source_audit=ROOT/'book/coverage/checks/root-source47-final-owner-integration20-v3.json'
for name in ['reports/full-coverage/lean-checkpoint-20/ledger-audit.json','reports/full-coverage/publication-checks/ledger-checkpoint-20.json']: assert sha(PUB/name)==sha(source_audit)
progress=read(PUB/'book/coverage/progress.json');assert progress['verified_checkpoint']['proof_files']==1068 and progress['verified_checkpoint']['theorems']==8667 and progress['current_documented_material_corrections']==47
assert progress['verified_checkpoint']['coverage_complete'] is False and progress['publication_status']=='checkpoint20_content_pushed_pages_size_repair_prepared'
excluded=[line[4:] for line in (PUB/'_config.yml').read_text().splitlines() if line.startswith('  - ')]
assert len(excluded)==48 and len(set(excluded))==48
included=sum(p.stat().st_size for p in PUB.rglob('*') if p.is_file() and '.git' not in p.relative_to(PUB).parts and not any(p.relative_to(PUB).as_posix()==x or p.relative_to(PUB).as_posix().startswith(x+'/') for x in excluded))
assert included<900_000_000
for argv in [['git','diff','--name-only','-z'],['git','diff','--cached','--name-only','-z'],['git','ls-files','--others','--exclude-standard','-z']]:
 dirty=subprocess.run(argv,cwd=PUB,capture_output=True,check=True).stdout
 assert {x.decode() for x in dirty.split(b'\0') if x}<=names
record=REPORTS/'pages20-repair-prestage-integrity-v1.json';assert not record.exists()
record.write_text(json.dumps(dict(status='passed_exact_assets_actual_evidence_literal_exclusion_repair',checked_at_utc=datetime.now(timezone.utc).isoformat(),config_sha256=sha(PUB/'_config.yml'),independent_review=str(peer.relative_to(ROOT)),independent_review_sha256=sha(peer),frozen20_assets_byte_exact=31,proof_sources_and_evidence_not_modified=True,published_file_budget_bytes=included,coverage_complete=False,paths_sha256=expected),indent=2)+'\n')
name=str(record.relative_to(ROOT));shutil.copyfile(record,PUB/name);names.add(name)
whitelist=REPORTS/'pages20-repair-staging-whitelist-v1.json';assert not whitelist.exists();whitelist.write_text(json.dumps(sorted(names),indent=2)+'\n')
pathspec=REPORTS/'pages20-repair-stage-pathspec-v1.nul';assert not pathspec.exists();pathspec.write_bytes(b''.join(name.encode()+b'\0' for name in sorted(names)))
command=['git','add','-f','--pathspec-from-file='+str(pathspec),'--pathspec-file-nul']
r=subprocess.run(command,cwd=PUB,capture_output=True)
staged={x.decode() for x in subprocess.run(['git','diff','--cached','--name-only','-z'],cwd=PUB,capture_output=True,check=True).stdout.split(b'\0') if x}
result=REPORTS/'pages20-repair-staging-execution-v1.json';assert not result.exists()
result.write_text(json.dumps(dict(status='passed_explicit_repair_whitelist_staged' if r.returncode==0 else 'failed',actual_exit_code=r.returncode,actual_command=command,actual_workdir=str(PUB),started_at_utc=started,finished_at_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-tick,stdout=r.stdout.decode(),stderr=r.stderr.decode(),checked_paths=len(names),staged_paths=len(staged),published_file_budget_bytes=included),indent=2)+'\n')
assert r.returncode==0 and staged and staged<=names
print(json.dumps(dict(status='passed',checked_paths=len(names),staged_paths=len(staged),included_bytes=included)))
