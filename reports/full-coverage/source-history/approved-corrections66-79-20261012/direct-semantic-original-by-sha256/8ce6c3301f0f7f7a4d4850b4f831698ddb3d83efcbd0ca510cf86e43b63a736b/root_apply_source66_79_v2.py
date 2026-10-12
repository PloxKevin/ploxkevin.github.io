"""Guard, reparse, preserve, and optionally apply fourteen reviewed literal patches.

Preparation and default application are read-only with respect to live sources.
Every actual isolated full29 parser finishes before history or live source writes.
"""
from pathlib import Path
from datetime import datetime,timezone
import argparse,contextlib,hashlib,importlib.util,io,json,re,subprocess,sys,tempfile,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3]
SELF='book/coverage/checks/root_apply_source66_79_v2.py'
PREP='book/coverage/checks/root_prepare_source66_79_contract_v2.py'
BASE='book/coverage/checks/root_apply_source54_55_v3.py'
BASE_SHA='6b4c52ce05d8ed940a22982107b2ba708dc0f6f28e1a60ab4396b78c68286be0'
PARSER='book/inventory_claims.py';PARSER_SHA='b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
VALIDATOR='book/validate.py';VALIDATOR_SHA='29617e224d7105c9f504bb1b0373b2c33b92dd9c03a951c88c965ec27c25be86'
INVENTORY='book/coverage/inventory.json';INV_SHA='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
CORRECTIONS='book/coverage/material-corrections.json';CORR_SHA='5c3a871bbc5782a02c5b19bfa33a8fa6e4dc311a9e72c525d76fcc526f37eafd'
SELECTION='reports/full-coverage/checkpoint-29-selection.json';SEL_SHA='ad4eb2940daa6f89dfb52390abc26c8bedb00dae7f97534957f5a4e87ac0d8a9'
MANIFEST='reports/full-coverage/checkpoint-29-manifest.json';MAN_SHA='0b7cf36595dca47925ad71ad030dae96de38d525fd0208f2144efa4c57351e4f'
METADATA='01b95073d2f78d066ef88c1aa3fd20af1d631e22'
PUB=ROOT/'reports/book/publication-repo'
CONTRACT_DIR='book/coverage/checks/future30-core/source66-79-contract-v2'
CONTRACT=CONTRACT_DIR+'/source66-79-fourteen-step-application-contract-v2.json'
REPORT='reports/full-coverage/source66-79-corrections-application-v2.json'
HISTORY='reports/full-coverage/source-history/approved-corrections66-79-20261012'
SUPPLY_PINS={'foundations':'71e3b464aebcf47cad35151bd0226b334880916e06849578d7ba23333d6b613c','modules':'5df8cb07cdf76e4997f80b57d1c4aeabf1402fbf4530cc724356ff2465fadca7','cmdp_proposal':'f2c4491a3b51d2e53e7e004f6e97adc143231cf43c9c3c557fbbc02b54a159f7','cmdp_peer':'761ed97f4b1a2e46270983420fd0ffd669fdd7dcc323b56dba534d2828a9fc81'}
def module(n,p):
 s=importlib.util.spec_from_file_location(n,ROOT/p);v=importlib.util.module_from_spec(s);s.loader.exec_module(v);return v
b=module('source66_79_pinned_parser_guard',BASE)
def path(n):
 assert type(n) is str and n and not any(c in n for c in '\0\n\r')
 p=Path(n)
 if not p.is_absolute():p=b.safe(n)
 assert p.is_file() and not p.is_symlink() and (p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to('/tmp'))
 return p

def ref(n):
 p=path(str(n));name=str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p)
 return {'file':name,'sha256':b.sha(p),'bytes':p.stat().st_size}
def checked(r):
 assert isinstance(r,dict) and type(r.get('file')) is str and re.fullmatch('[0-9a-f]{64}',r.get('sha256',''))
 p=path(r['file']);assert b.sha(p)==r['sha256'],r['file']
 if 'bytes' in r:assert type(r['bytes']) is int and r['bytes']==p.stat().st_size
 return p

def aliases(d,keys,expected,kind):
 vs=[d[k] for k in keys if k in d];assert vs and all(type(v) is kind and v==expected for v in vs),(keys,vs)
def native(r,expected_command=None,expected_cwd=None):
 p=checked(r);d=b.read(p);assert d['status'].startswith('passed')
 aliases(d,['actual_exit_code','exit_code','actual_runner_exit_code'],0,int)
 cmd=d.get('actual_command',d.get('command'));cwd=d.get('actual_workdir',d.get('working_directory',d.get('cwd',d.get('workdir'))))
 aliases(d,['actual_command','command'],cmd,list);aliases(d,['actual_workdir','working_directory','cwd','workdir'],cwd,str)
 if expected_command is not None:assert cmd==expected_command
 if expected_cwd is not None:assert cwd==expected_cwd
 log=d.get('raw_log',d.get('log'));digest=d.get('raw_log_sha256',d.get('log_sha256'))
 if isinstance(log,dict):row=log;checked(row)
 else:
  aliases(d,['raw_log','log'],log,str);aliases(d,['raw_log_sha256','log_sha256'],digest,str);row={'file':log,'sha256':digest};checked(row)
 if 'helper_sha256_before' in d or 'helper_sha256_after' in d:
  assert isinstance(d['helper_sha256_before'],dict) and d['helper_sha256_before'] and d['helper_sha256_before']==d['helper_sha256_after']
 return d,[ref(str(p)),ref(str(checked(row)))]

def helpers():return {n:b.sha(path(n)) for n in [PREP,SELF]}
def guards():
 assert Path(__file__).resolve()==ROOT/SELF
 for n,h in [(BASE,BASE_SHA),(PARSER,PARSER_SHA),(VALIDATOR,VALIDATOR_SHA),(INVENTORY,INV_SHA),(CORRECTIONS,CORR_SHA),(SELECTION,SEL_SHA),(MANIFEST,MAN_SHA)]:assert b.sha(path(n))==h,n
 corrections=b.read(path(CORRECTIONS));assert len(corrections['corrections'])==65
 assert [r['correction_id'] for r in corrections['corrections'][-5:]]==[61,62,63,64,65]
 selection=b.read(path(SELECTION));manifest=b.read(path(MANIFEST))
 assert selection['proof_file_count']==1197 and len(selection['proof_files'])==1197
 assert manifest['status']=='formal_verification_passed_partial_coverage' and manifest['coverage_complete'] is False and len(manifest['proof_files'])==1197
 proofs={n:r['sha256'] for n,r in selection['proof_files'].items()};assert all(manifest['proof_files'][n]['sha256']==h for n,h in proofs.items())
 assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')}
 owners={n:h for n,h in manifest['working_inputs_sha256'].items() if n in {f'book/coverage/{x}.json' for x in ['core','foundations','applied','modules','applied-promotions']}}
 assert len(assets)==31 and len(owners)==5
 for n,h in {**proofs,**assets,**owners}.items():assert b.sha(path(n))==h,n
 assert b.read(path(INVENTORY))['counts']['exercises']==556 and b.read(path(INVENTORY))['counts']['material_source_units']==12774
 for a in [['rev-parse','HEAD'],['ls-remote','origin','refs/heads/main']]:
  r=subprocess.run(['git',*a],cwd=PUB,capture_output=True,check=True);values=r.stdout.decode().split();assert values==([METADATA] if a[0]=='rev-parse' else [METADATA,'refs/heads/main'])
 live=b.read(path('reports/full-coverage/live-checkpoint-29-attempt1.json'));pages=b.read(path('reports/full-coverage/pages-checkpoint-29-attempt1.json'))
 assert live['status']=='passed_all31_asset_sha256' and live['commit']==live['remote_main']==pages['commit']==pages['expected_commit']==METADATA
 assert len(live['assets'])==31 and {r['source']:r['expected_sha256'] for r in live['assets']}==assets
 assert all(r['matches'] is True and r['http_status']==200 and r['actual_sha256']==r['expected_sha256'] for r in live['assets'])
 assert pages['status']=='passed' and pages['build_status']=='built'
 native(ref('reports/full-coverage/pages-checkpoint-29-attempt1.json'),['gh','api','repos/PloxKevin/ploxkevin.github.io/pages/builds/latest'],str(PUB))
 r=ref('reports/full-coverage/live29-current-metadata-confirmation-execution-v1.json')
 actual,ev=native(r,['python3','book/coverage/verify_live19.py','29',METADATA,'--attempt','1'],str(ROOT))
 assert actual['helper_sha256_before']==actual['helper_sha256_after']=={'book/coverage/verify_live19.py':b.sha(path('book/coverage/verify_live19.py'))}
 assert actual['selection29_before']==actual['selection29_after']=={'file':SELECTION,'sha256':SEL_SHA}
 assert not (ROOT/REPORT).exists() and not (ROOT/HISTORY).exists()
 for num in range(66,80):
  for label in ['before','after']:assert not (ROOT/f'book/coverage/inventory-{label}-correction{num}.json').exists()
 return {'proofs':proofs,'assets':assets,'owners':owners,'selection':ref(SELECTION),'manifest':ref(MANIFEST),'inventory':ref(INVENTORY),'corrections':ref(CORRECTIONS),'metadata_commit':METADATA,'current_metadata_confirmation':r,'delivery_evidence':[r,*ev,ref('reports/full-coverage/live-checkpoint-29-attempt1.json'),ref('reports/full-coverage/pages-checkpoint-29-attempt1.json'),ref('reports/full-coverage/pages-checkpoint-29-attempt1.log')]}

def shape(data):
 sys.path.insert(0,str(ROOT/'book'));from validate import Document
 return [(n.tag,n.attrs,n.line) for n in Document(data.decode()).nodes]
def forward_inverse(original,replacements):
 text=original.decode();assert replacements
 for r in replacements:
  assert type(r['before']) is str and type(r['after']) is str and r['before']!=r['after']
  assert text.count(r['before'])==1 and r['after'] not in text;rtext=text.replace(r['before'],r['after'],1);text=rtext
 result=text.encode();assert original.count(b'\n')==result.count(b'\n') and shape(original)==shape(result)
 for r in reversed(replacements):assert text.count(r['after'])==1;text=text.replace(r['after'],r['before'],1)
 assert text.encode()==original;return result

def peer_read(r):
 d=b.read(checked(r));assert d['status'].startswith('passed') and d['errors']==[]
 keys=['actual_finalizer','actual_reader','actual_independent_reader','actual_reader_execution','actual_reader_execution_v2']
 rr=next((d[k] for k in keys if isinstance(d.get(k),dict) and 'file' in d[k]),None)
 assert rr is not None,'Peer lacks a genuine success-native pointer'
 _,ev=native(rr);return d,[ref(str(checked(r))),*ev]

def proposal_steps(supplies):
 f=b.read(checked(supplies['foundations']));m=b.read(checked(supplies['modules']));c=b.read(checked(supplies['cmdp_proposal']));cp,ce=peer_read(supplies['cmdp_peer'])
 assert len(f['proposals'])==6 and len(m['individual_unnumbered_proposals'])==7 and cp['narrow_wording_approved'] is True
 assert cp['request']['sha256']=='71159420f8cd065e5f29af9660d947c0b99a8a2d295fcde8cc91fe280ed84fc6'
 req=b.read(checked(cp['request']));assert req['original_exact_author_preparation_proposal']['sha256']==supplies['cmdp_proposal']['sha256']
 rows=[]
 for x in f['proposals']:
  rows.append({'label':x['family'],'proposal':x['proposal'],'peer':x['full_wording_and_actual_isolated_both_ROOT_OUT29_parser_peer'],'source':x['source_relative_path'],'base':x['base_original_page'],'individually_proposed':x['proposed_entire_page'],'replacements':x['exact_replacements'],'changed':{'exercises':[],'material_source_units':x['exact_changed_literal_keys']},'math_peers':x['full_mathematical_scope_peers']+x['additional_full_prospective_literal_associations']})
 for x in m['individual_unnumbered_proposals']:
  rows.append({'label':x['id'],'proposal':x['unnumbered_proposal'],'peer':x['independent_narrow_full_literal_parser_peer'],'source':'SafeLearning/'+x['exact_changed_literal_keys']['material_source_units'][0].split('::')[0],'base':x['immutable_current_source'],'individually_proposed':x['immutable_proposed_source'],'replacements':x['exact_replacements'],'changed':x['exact_changed_literal_keys'],'math_peers':[x['independent_full_mathematical_peer']]})
 rows.append({'label':'CMDP_qualified_drift_objective_theorem','proposal':supplies['cmdp_proposal'],'peer':supplies['cmdp_peer'],'source':'SafeLearning/cmdp.html','base':c['original_current_page'],'individually_proposed':c['proposed_source'],'replacements':c['four_exact_literal_substitutions'],'changed':c['fresh_changed_literal_keys'],'math_peers':[c['qualified48_full_independent_math_peer'],c['bounded_objective51_full_independent_math_peer']]})
 evidence=list(supplies.values());used=[]
 for i,x in enumerate(rows,66):
  assert x['source'].startswith('SafeLearning/') and x['source'].endswith('.html')
  original=path(x['source']).read_bytes();assert hashlib.sha256(original).hexdigest()==x['base']['sha256'];checked(x['base']);assert checked(x['base']).read_bytes()==original
  proposal=b.read(checked(x['proposal']));pd,ev=peer_read(x['peer']);evidence += [x['proposal'],x['individually_proposed'],*ev]
  # Successful reading alone does not imply a semantic narrow approval.
  if 'individual_wording_decisions' in pd:
   assert pd['individual_wording_decisions'] and all(z['approved'] is True for z in pd['individual_wording_decisions'])
  else:
   approved=[pd[k] for k in ['narrow_wording_approved','narrow_two_replacement_proposal_approved','narrow_single_replacement_proposal_approved'] if k in pd]
   assert approved and all(z is True for z in approved)
  flags=[pd[k] for k in ['both_parser_ROOT_and_OUT_strictly_TMP','both_ROOT_and_OUT_strictly_TMP'] if k in pd]
  if not flags and 'independent_parser' in pd:
   assert pd['independent_parser']['both_ROOT_and_OUT_TMP'] is True
  else:assert flags and all(z is True for z in flags)
  bound=pd.get('proposal',pd.get('request'))
  assert bound is not None
  if x['label']=='CMDP_qualified_drift_objective_theorem':assert bound['sha256']==cp['request']['sha256']
  else:assert bound['sha256']==x['proposal']['sha256']
  for key in ['actual_author_parser_preparation','author_actual_preparation','author_actual_parser','actual_author_preparation']:
   if isinstance(pd.get(key),dict) and 'file' in pd[key]:
    _,author_evidence=native(pd[key]);evidence.extend(author_evidence)
  assert forward_inverse(original,x['replacements'])==checked(x['individually_proposed']).read_bytes()
  # Every supplied substitution is one of the pinned independently reviewed proposal bytes.
  declared=proposal.get('exact_replacements',proposal.get('four_exact_literal_substitutions'))
  assert declared==x['replacements']
  for r in x['math_peers']:
   md=b.read(checked(r));assert md['status'].startswith(('passed','approved')) and md.get('errors',[])==[];evidence.append(r)
  for r in x['replacements']:
   assert not any(r['before'] in z or z in r['before'] or r['after'] in z or z in r['after'] for source,z in used if source==x['source'])
   used += [(x['source'],r['before']),(x['source'],r['after'])]
  x['correction_id']=i;x['individual_review_baseline_source65_sha256']=x['base']['sha256']
 assert len(rows)==14 and [x['correction_id'] for x in rows]==list(range(66,80))
 return rows,evidence

def parser_worker(control,control_sha,out):
 p=path(control);assert b.sha(p)==control_sha;d=b.read(p)
 candidates={n:checked(r).read_bytes() for n,r in d['candidates'].items()}
 assert all(n.startswith('SafeLearning/') and n.endswith('.html') for n in candidates)
 data,_=b.full_parser(candidates)
 output=Path(out);assert output.is_absolute() and output.resolve().is_relative_to('/tmp') and not output.exists()
 b.write_new(output,data)

def fresh_parse(candidates,record_dir,step):
 with tempfile.TemporaryDirectory(prefix='source66-79-native-parser-') as td:
  temp=Path(td);controls={}
  for i,(n,data) in enumerate(candidates.items()):
   q=temp/f'candidate-{i}.html';b.write_new(q,data);controls[n]=ref(str(q))
  control=temp/'control.json';b.write_new(control,b.encoded({'candidates':controls}));output=temp/'inventory.json'
  command=['python3',str(ROOT/SELF),'--parser-worker',str(control),'--parser-sha256',b.sha(control),'--parser-output',str(output)]
  before_helpers=helpers();start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();done=subprocess.run(command,cwd=ROOT,capture_output=True)
  finish=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick
  log=record_dir/f'parser-step{step}.log';b.write_new(log,done.stdout+done.stderr)
  retained={}
  for i,q in enumerate([control,*[path(r['file']) for r in controls.values()]]):
   preserved=record_dir/f'parser-step{step}-input{i}-original{Path(q).suffix}'
   b.write_new(preserved,q.read_bytes());retained[str(q)]=ref(str(preserved))
  record={'status':'passed_actual_isolated_full29_parser' if done.returncode==0 else 'failed_actual_isolated_full29_parser','actual_command':command,'actual_workdir':str(ROOT),'actual_exit_code':done.returncode,'helper_sha256_before':before_helpers,'helper_sha256_after':helpers(),'started_at_utc':start,'finished_at_utc':finish,'elapsed_seconds':elapsed,'raw_log':ref(str(log)),'parser_sha256_before':PARSER_SHA,'parser_sha256_after':b.sha(path(PARSER)),'both_parser_ROOT_and_OUT_strictly_TMP':True,'original_TMP_control_and_candidate_paths_are_historical':True,'exact_original_TMP_input_byte_aliases':retained,'actual_parser_output_inventory_sha256':b.sha(output) if output.is_file() else None,'live_source_inventory_owner_or_canonical_mutation':False}
  rp=record_dir/f'parser-step{step}-actual.json';b.write_new(rp,b.encoded(record));assert done.returncode==0 and record['parser_sha256_after']==PARSER_SHA and record['helper_sha256_before']==record['helper_sha256_after']
  data=output.read_bytes();return data,json.loads(data),ref(str(rp)),ref(str(log))

def semantic_inventory(d):return {k:v for k,v in d.items() if k not in ['generated_at_utc']}
def writer_review(r):
 d,ev=peer_read(r);assert d['reviewed_helpers_sha256']==helpers()
 assert d['full_code_read'] is True;return ev

def evaluate(contract,worker_dir):
 baseline=guards();assert contract['status']=='prepared_exact_fourteen_step_source66_to79_contract_only'
 assert contract['reviewed_helpers_sha256']==helpers() and contract['baseline']==baseline
 assert [s['correction_id'] for s in contract['steps']]==list(range(66,80))
 for name,r in contract['input_supplies'].items():assert r['sha256']==SUPPLY_PINS[name];checked(r)
 rows,_=proposal_steps(contract['input_supplies']);assert len(rows)==len(contract['steps'])
 candidates={};previous=b.read(path(INVENTORY));parsed=[]
 for raw,step in zip(rows,contract['steps']):
  for k in ['correction_id','label','source','proposal','peer','replacements','changed','individual_review_baseline_source65_sha256']:assert step[k]==raw[k]
  before=candidates.get(step['source'],path(step['source']).read_bytes());assert hashlib.sha256(before).hexdigest()==step['source_sha256_before']
  new=forward_inverse(before,step['replacements']);assert new==checked(step['candidate']).read_bytes();candidates[step['source']]=new
  data,following,native_ref,log=fresh_parse(candidates,worker_dir,step['correction_id'])
  sd={'source':step['source'],'candidate':step['candidate'],'counts':previous['counts'],'exact_changed_text_keys':step['changed']}
  changed=b.inventory_diff(previous,following,sd)
  expected=b.read(checked(step['inventory_after']));assert semantic_inventory(following)==semantic_inventory(expected)
  assert following['counts']['exercises']==556 and following['counts']['material_source_units']==12774
  parsed.append((step,new,data,changed,native_ref,log));previous=following
 assert previous['source_sha256']==contract['final_source_sha256'] and guards()==baseline and helpers()==contract['reviewed_helpers_sha256']
 return baseline,parsed

def copy_plan(contract,writer):
 plan={};aliases={}
 def put(target,r):
  p=checked(r);assert not (ROOT/target).exists();assert target not in plan or plan[target]['sha256']==r['sha256'];plan[target]=ref(str(p));aliases[r['file']]={'file':target,'sha256':r['sha256']}
 for n in [INVENTORY,CORRECTIONS,*contract['baseline']['owners'],*{s['source'] for s in contract['steps']}]:put(HISTORY+'/source65-owner29-original/'+n,ref(n))
 for r in [*contract['bounded_original_evidence'],ref(CONTRACT),ref(PREP),ref(SELF),writer]:
  p=checked(r)
  assert '/.lake/' not in str(p) and not any(f'checkpoint-{i}/' in str(p) for i in range(1,28))
  put(HISTORY+'/direct-semantic-original-by-sha256/'+r['sha256']+'/'+p.name,r)
 for num in range(66,80):
  for label in ['before','after']:assert not (ROOT/f'book/coverage/inventory-{label}-correction{num}.json').exists()
  assert not (ROOT/HISTORY/f'material-corrections-before{num}-original.json').exists()
 assert not (ROOT/HISTORY/'preserved-history-v1.json').exists() and not (ROOT/REPORT).exists()
 return plan,aliases

def application(args):
 cr={'file':args.contract,'sha256':args.contract_sha256};assert ref(str(checked(cr)))['file']==CONTRACT
 contract=b.read(checked(cr));wr={'file':args.writer_peer,'sha256':args.writer_peer_sha256};writer_review(wr)
 plan,alias=copy_plan(contract,wr)
 with tempfile.TemporaryDirectory(prefix='source66-79-readiness-') as td:
  baseline,parsed=evaluate(contract,Path(td))
  # Retain every genuine fresh parser native/log/control/candidate byte without copying trees.
  for original in Path(td).iterdir():
   r=ref(str(original));target=HISTORY+'/actual-application-parsers/'+original.name
   assert not (ROOT/target).exists() and target not in plan
   plan[target]=r;alias[str(original)]={'file':target,'sha256':r['sha256']}
  for original in Path(td).glob('parser-step*-actual.json'):
   parser_record=b.read(original)
   for historical,r in parser_record['exact_original_TMP_input_byte_aliases'].items():
    assert r['file'] in alias and alias[r['file']]['sha256']==r['sha256']
    alias[historical]=alias[r['file']]
  # The complete fresh14 parses and all preservation/collision guards precede every write.
  if not args.apply:
   print(json.dumps({'status':'passed_readonly_source66_to79_fourteen_parser_preflight','contract':ref(CONTRACT),'steps':14,'source_writes':False,'coverage_complete':False}));return
  assert guards()==baseline
  for n,r in plan.items():checked(r);assert not (ROOT/n).exists()
  for n,r in plan.items():b.write_new(ROOT/n,checked(r).read_bytes())
  history=HISTORY+'/preserved-history-v1.json'
  b.write_new(ROOT/history,b.encoded({'status':'exact_source65_owner29_and_direct_fourteen_review_provenance_preserved','preserved_at_utc':datetime.now(timezone.utc).isoformat(),'original_byte_aliases':alias,'original_bodies_native_times_and_failures_unchanged':True,'historical_earlier_snapshot_or_lake_trees_copied':False,'baseline_metadata_commit':METADATA,'coverage_complete':False}))
  corrections=b.read(path(CORRECTIONS));apps=[]
  for step,new,data,changed,nr,log in parsed:
   num=step['correction_id'];assert len(corrections['corrections'])==num-1 and b.sha(path(step['source']))==step['source_sha256_before']
   before=f'book/coverage/inventory-before-correction{num}.json';after=f'book/coverage/inventory-after-correction{num}.json'
   b.write_new(ROOT/before,path(INVENTORY).read_bytes());b.write_new(ROOT/HISTORY/f'material-corrections-before{num}-original.json',path(CORRECTIONS).read_bytes())
   at=datetime.now(timezone.utc).isoformat();path(step['source']).write_bytes(new);path(INVENTORY).write_bytes(data);b.write_new(ROOT/after,data)
   archived_parser=HISTORY+'/actual-application-parsers/'+Path(nr['file']).name;archived_log=HISTORY+'/actual-application-parsers/'+Path(log['file']).name
   assert b.sha(path(archived_parser))==nr['sha256'] and b.sha(path(archived_log))==log['sha256']
   corrections['corrections'].append({'correction_id':num,'source':step['source'],'before_sha256':step['source_sha256_before'],'after_sha256':step['candidate']['sha256'],'replacements':step['replacements'],'corrected_at_utc':at,'status':'source_corrected_exact_independently_reviewed_literal_scope_owner_identity_rebase_pending','source_proposal':alias[step['proposal']['file']],'independent_semantic_review':alias[step['peer']['file']],'individual_review_source65_sha256':step['individual_review_baseline_source65_sha256'],'cumulative_candidate_identity_distinct_from_individual_reviewed_page':True,'historical_source':alias[step['source']],'preserved_history':ref(history),'inventory_before':ref(before),'inventory_after':ref(after),'actual_fresh_parser':ref(archived_parser),'scope':'Exact source literal correction only; every old mathematical body/status/native history remains intact. Owner identity rebasing and whole promotions require separate reviewed integration.'})
   path(CORRECTIONS).write_bytes(b.encoded(corrections));assert b.sha(path(step['source']))==step['candidate']['sha256'];apps.append({'correction_id':num,'applied_at_utc':at,'source_after':ref(step['source']),'inventory_before':ref(before),'inventory_after':ref(after),'changed_text_keys':changed,'actual_parser':ref(archived_parser),'actual_parser_raw_log':ref(archived_log)})
  changed_pages={s['source'] for s in contract['steps']}
  for n,h in {**baseline['proofs'],**baseline['owners'],**{n:h for n,h in baseline['assets'].items() if n not in changed_pages}}.items():assert b.sha(path(n))==h,n
  assert len(b.read(path(CORRECTIONS))['corrections'])==79 and b.read(path(INVENTORY))['source_sha256']==contract['final_source_sha256']
  record={'status':'passed_actual_source66_to79_fourteen_reviewed_literal_corrections_owner_rebase_pending','helper':ref(SELF),'contract':ref(CONTRACT),'writer_peer':wr,'applications':apps,'preserved_history':ref(history),'before_inventory':contract['baseline']['inventory'],'after_inventory':ref(INVENTORY),'after_corrections':ref(CORRECTIONS),'selected29_1197_sources_unchanged':True,'five_installed29_raw_owners_unchanged':True,'remaining_assets_unchanged':31-len(changed_pages),'baseline_delivery_only':METADATA,'coverage_complete':False}
  b.write_new(ROOT/REPORT,b.encoded(record));print(json.dumps({'status':record['status'],'report':ref(REPORT),'inventory':ref(INVENTORY),'corrections':ref(CORRECTIONS),'coverage_complete':False}))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--contract');p.add_argument('--contract-sha256');p.add_argument('--writer-peer');p.add_argument('--writer-peer-sha256');p.add_argument('--apply',action='store_true');p.add_argument('--parser-worker');p.add_argument('--parser-sha256');p.add_argument('--parser-output');a=p.parse_args()
 if a.parser_worker:
  assert a.parser_sha256 and a.parser_output and not a.apply and not a.contract;parser_worker(a.parser_worker,a.parser_sha256,a.parser_output)
 else:
  assert a.contract and a.contract_sha256 and a.writer_peer and a.writer_peer_sha256 and not a.parser_output;application(a)
