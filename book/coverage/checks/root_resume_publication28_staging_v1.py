"""Finish the actual byte-checked index while retaining exact native whitespace."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess,importlib.util
ROOT=Path(__file__).resolve().parents[3];PUB=ROOT/'reports/book/publication-repo'
SELF='book/coverage/checks/root_resume_publication28_staging_v1.py'
PLAN='book/coverage/checks/future28-core/root-explicit-audited28-publication-stage-plan-v1.json'
REPORT='reports/full-coverage/publication28-staged-byte-check-v1.json'
FAILED='reports/full-coverage/stage-publication28-execution-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_bytes())
def git(a,data=None,check=True):return subprocess.run(['git',*a],cwd=PUB,input=data,capture_output=True,check=check)
spec=importlib.util.spec_from_file_location('original28stage',ROOT/'book/coverage/checks/root_stage_publication28_v6.py');s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
assert sha(ROOT/'book/coverage/checks/root_stage_publication28_v6.py')=='68e80bf6b9259e18e2813e5b64bd9b60ba8add4168a198b9d9bffd3a3f31431f'
plan=read(PLAN);assert sha(ROOT/PLAN)=='345a89fe0be7c5dba487445194bbaf199c24cc4b2ddfe253a1d3f0a90f6fb1ad'
f=read(FAILED);assert f['status']=='failed' and type(f['actual_exit_code']) is int and f['actual_exit_code']==1
assert f['actual_command']==['python3','book/coverage/checks/root_stage_publication28_v6.py','--plan',PLAN,'--plan-sha256',sha(ROOT/PLAN),'--apply'] and f['actual_workdir']==str(ROOT)
assert sha(ROOT/f['log'])==f['log_sha256']=='875ce499854712ea800ee0454a703d152710255870032dbe641e73b2c53ef720'
assert 'assert n.endswith' in (ROOT/f['log']).read_text()
assert git(['rev-parse','HEAD']).stdout.decode().strip()==plan['baseline_publication_head']=='8fa808699674d13e4297d226ef1530a7ec744ad0'
assert not (ROOT/REPORT).exists() and not (PUB/REPORT).exists()
m=s.checked(plan['manifest']);selection=s.checked(plan['selection']);audit=s.checked(plan['original_audit'])
assert m['status']=='formal_verification_passed_partial_coverage' and m['coverage_complete'] is False
assert (audit['proof_file_count'],audit['theorem_count'])==(1186,9896) and audit['status']=='passed'
assert audit['proof_sha256']=={n:r['sha256'] for n,r in selection['proof_files'].items()}
frozen=m['frozen_inputs_sha256'];extra=plan['supplementary_paths_sha256'];expected={}
for n in s.checked(plan['prepared_file_list']):
 if n in {'book/coverage/progress.json','reports/full-coverage/README.md'}:h=extra[n]
 elif n in frozen:h=frozen[n]
 elif n.startswith('reports/full-coverage/checkpoint-28/reports/full-coverage/source-history/'):h=frozen[n.removeprefix('reports/full-coverage/checkpoint-28/')]
 else:h=sha(s.safe(ROOT,n))
 expected[n]=h
for n,h in extra.items():assert sha(s.safe(ROOT,n))==h and (n not in expected or expected[n]==h);expected[n]=h
expected[PLAN]=sha(ROOT/PLAN);config=s.checked(plan['configuration_preparation']);expected['_config.yml']=config['config_sha256']
assert all(sha(s.safe(PUB,n))==h for n,h in expected.items())
assert config['exact_selected_lean_sources_in_git_archive_sha256']==audit['proof_sha256']
assert [line[4:] for line in (PUB/'_config.yml').read_text().splitlines() if line.startswith('  - ')]==config['exclusions'] and len(config['exclusions'])==156
for n,h in m['working_inputs_sha256'].items():
 if n.startswith(('SafeLearning/','verification/lean/')) or n in {'book/coverage/'+v+'.json' for v in ['core','foundations','applied','modules','applied-promotions']}:assert sha(s.safe(ROOT,n))==h
assert all(sha(s.safe(ROOT,n))==sha(s.safe(PUB,n))==h for n,h in audit['proof_sha256'].items())
names={n.decode() for n in git(['diff','--cached','--name-only','-z']).stdout.split(b'\0') if n};assert names and names<=set(expected)
assert not git(['diff','--name-only','-z']).stdout
for row in git(['status','--porcelain','-z','--untracked-files=all']).stdout.decode().split('\0'):
 if row:assert row[:2] in ('M ','A ') and row[3:] in names
entries={}
for row in git(['ls-files','--stage','-z']).stdout.split(b'\0'):
 if row:
  header,n=row.split(b'\t',1);mode,oid,stage=header.split();assert stage==b'0';entries[n.decode()]=(mode,oid)
ordered=sorted(names);oids=git(['hash-object','--stdin-paths','--no-filters'],''.join(str(s.safe(PUB,n))+'\n' for n in ordered).encode()).stdout.splitlines()
assert len(oids)==len(ordered) and all(entries[n][0] in (b'100644',b'100755') and entries[n][1]==oid for n,oid in zip(ordered,oids))
CROWN='verification/lean/SafeLearning/CompleteModulesCrownOtherRadii28.lean'
SNAPSHOT='book/coverage/checks/future28-core/current60-canonical-pairs-v1/source-snapshots/CompleteModulesCrownOtherRadii28.lean'
assert sha(ROOT/CROWN)==sha(ROOT/SNAPSHOT)==audit['proof_sha256'][CROWN]
allowed_special={CROWN:{(119,'trailing whitespace.'),(121,'trailing whitespace.')},SNAPSHOT:{(119,'trailing whitespace.'),(121,'trailing whitespace.')}}
browser_expected={
 'barriers.html':{217,604,607},'cmdp.html':{458,509},'toolkit-gp.html':{131,146,269,409,525,691},'toolkit-lmi.html':{215,375,564},'viability.html':{583}}
for page,lines in browser_expected.items():
 n='reports/full-coverage/browser-input28-source60/SafeLearning/'+page
 assert sha(ROOT/n)==sha(ROOT/'SafeLearning'/page)==frozen['SafeLearning/'+page]
 allowed_special[n]={(line,'trailing whitespace.') for line in lines}
lint=git(['diff','--cached','--check'],check=False);assert lint.returncode==2 and not lint.stderr
lines=lint.stdout.decode().splitlines();i=0;violations={};seen={n:set() for n in allowed_special}
while i<len(lines):
 match=re.fullmatch(r'(.+):([0-9]+): (trailing whitespace\.|new blank line at EOF\.|space before tab in indent\.)',lines[i]);assert match,lines[i];i+=1
 n,line,kind=match[1],int(match[2]),match[3]
 if kind!='new blank line at EOF.':assert i<len(lines) and lines[i].startswith('+');i+=1
 assert n in names and sha(s.safe(ROOT,n))==sha(s.safe(PUB,n))==expected[n]
 if n in allowed_special:assert (line,kind) in allowed_special[n];seen[n].add((line,kind))
 else:assert not n.startswith(('SafeLearning/','verification/lean/')) and (n.endswith('.log') or '/source-history/' in n or '/original-' in n)
 violations.setdefault(n,{'sha256':expected[n],'diagnostics':[]})['diagnostics'].append({'line':line,'kind':kind})
assert seen==allowed_special
git(['diff','--cached','--check','--','.',*[':(literal,exclude)'+n for n in sorted(violations)]])
record={'status':'passed_exact_audited_checkpoint28_staged_bytes','checked_at_utc':datetime.now(timezone.utc).isoformat(),
 'baseline_head':plan['baseline_publication_head'],'plan':{'file':PLAN,'sha256':sha(ROOT/PLAN)},'staged_paths_sha256':{n:expected[n] for n in ordered},
 'exact_original_archival_whitespace':violations,'sources':1186,'public_theorems':9896,'coverage_complete':False,'delivery_pending':True,
 'original_failed_staging_execution':{'file':FAILED,'sha256':sha(ROOT/FAILED)},
 'exact_selected_source_whitespace':{'file':CROWN,'sha256':audit['proof_sha256'][CROWN],'diagnostics':[{'line':119,'kind':'trailing whitespace.'},{'line':121,'kind':'trailing whitespace.'}],'scope':'Two already compiled and source-reviewed whitespace suffixes preserved exactly; no proof or audit byte changes.'},
 'additional_snapshot_whitespace':{n:violations[n] for n in allowed_special if n!=CROWN}}
b=(json.dumps(record,separators=(',',':'))+'\n').encode();assert s.website_size()+len(b)<850000000
assert all(sha(s.safe(PUB,n))==h for n,h in expected.items())
for base in [ROOT,PUB]:
 with s.safe(base,REPORT).open('xb') as file:file.write(b)
git(['add','-f','--',REPORT]);assert hashlib.sha256(git(['show',':'+REPORT]).stdout).hexdigest()==sha(ROOT/REPORT)
print(json.dumps({'status':record['status'],'staged_paths':len(names)+1,'whitespace_files':len(violations),'exact_selected_source_whitespace_lines':2,'coverage_complete':False}))
