from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json,re,subprocess,sys,types

R=Path('/home/oxrexkevin/SafetyBased')
HELPER=R/'book/coverage/checks/run_root28_current60_commissioning17_canonical_pair_v1.py'
ORIGINAL=R/'book/coverage/checks/run_root28_current60_canonical_pairs_v2.py'
PLAN=Path('/tmp/root28-current60-commissioning17-canonical-plan-v1.json')
OUT=Path('/tmp/root28-commissioning17-executor-independent-modules28-reader-v1.json')
START=datetime.now(timezone.utc).isoformat()
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p):return json.loads(Path(p).read_bytes())
def P(n):return Path(n)if Path(n).is_absolute()else R/n
def ref(p):return {'file':str(p),'sha256':H(p),'bytes':Path(p).stat().st_size}
def checked(r):
    p=P(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];return p
assert H(HELPER)=='31e8f7db0df1b405ce3a63941e598af0ef5d39488cdf9e37e629fe66b6c4b38d'
assert H(ORIGINAL)=='69a8eab0c5710ea143dde3c72ecf08c5c6811fa87536cec688c3fe2ea7afbe83'
assert H(PLAN)=='3b11806ce0bd028ee2997b93d437c69b6d415683e792bfc3ca83498ffbc2a638'
old=ORIGINAL.read_text();new=HELPER.read_text();plan=J(PLAN);author=checked(plan['prepared_by']);author_text=author.read_text()
# Reconstruct the exact full delta from the author's fixed replacements, without executing its writes.
tree=ast.parse(author_text)
replacement_node=next(n.value for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='replacements'for t in n.targets))
replacements=ast.literal_eval(replacement_node)
prefix_node=next(n.value for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='prefix'for t in n.targets))
prefix=ast.literal_eval(prefix_node)
assert len(replacements)==13
rebuilt=old
for a,b in replacements.items():assert rebuilt.count(a)==1;rebuilt=rebuilt.replace(a,b)
assert rebuilt.count('    names, exported = set(), set()\n')==1
rebuilt=rebuilt.replace('    names, exported = set(), set()\n',prefix+'    names, exported = set(), set()\n')
assert rebuilt==new
assert prefix.startswith('    # Hold the ten completed new modules') and 'protected[row[\'canonical_source\']]'in prefix and "for key in ('actual_record','raw_log','source_snapshot')"in prefix
assert len(plan['sources'])==plan['source_count']==1 and plan['public_theorem_count']==17
row=plan['sources'][0];source=checked(row['original_tmp_source']);source_text=source.read_text()
assert H(source)=='bb74fce90694edb80f78e00d12582c7580314802a622d704271f6b876e7a7544'
request=J(checked(plan['original_scope_plans'][0]));peer_p=checked(row['independent_whole_scope_peer']);peer=J(peer_p)
assert row['public_declarations']==request['public_theorem_names']
bare=re.findall(r'^(?:theorem|lemma)\s+([A-Za-z0-9_]+)',source_text,re.M)
assert len(bare)==len(set(bare))==17 and bare==[n.rsplit('.',1)[1]for n in row['public_declarations']]
assert peer['status']=='passed_independent_full17_source_two_whole_commissioning_literals_review'and peer['errors']==[]and peer['source']==row['original_tmp_source']
assert peer['all17_complete_public_bodies_private_relu_QC_and_definitions_read']is True and peer['public_theorem_count']==17
assert {r['inventory_key']for r in peer['material_units']}=={'lipsdp.html::node-972','lipsdp.html::node-974'}
assert all(r['whole_unit_approved']is True and r['missing_clauses']==[]for r in peer['material_units'])
assert peer['whole976_sharp_lipschitz_constant_approved']is False
peer_actual=J(checked(peer['actual_reader_execution']));assert type(peer_actual['actual_exit_code'])is int and peer_actual['actual_exit_code']==0
inventory=J(R/'book/coverage/inventory.json');units={r['key']:r for r in inventory['material_source_units']}
for unit in peer['material_units']:assert unit['entire_current60_inventory_record']==units[unit['inventory_key']]
trial=J(checked(row['original_actual_tmp_trial']));assert type(trial['actual_exit_code'])is int and trial['actual_exit_code']==0
assert trial['actual_command']==['lake','env','lean',str(source)]and trial['source_sha256_before']==trial['source_sha256_after']==H(source)
checked({'file':trial['raw_log'],'sha256':trial['raw_log_sha256']});checked({'file':trial['source_snapshot'],'sha256':trial['source_snapshot_sha256']})
prior_p=checked(plan['prior_completed_pairs']);prior=J(prior_p);actual_p=checked(plan['prior_completed_pair_execution']);actual=J(actual_p)
assert prior['source_count']==len(prior['sources'])==10 and prior['actual_compiler_command_count']==len(prior['actual_paired_records'])==20
assert H(prior_p)=='209f306bc9c9b70b51a4eca063f453d546353bd9860ac3a96c6a3e4e037cc453'
assert type(actual['actual_exit_code'])is int and actual['actual_exit_code']==0
assert actual['helper_sha256_before']==actual['helper_sha256_after']=={'book/coverage/checks/run_root28_current60_canonical_pairs_v2.py':H(ORIGINAL)}
priorlog=checked({'file':actual['log'],'sha256':actual['log_sha256']});priorlog.read_text()
canonical={r['canonical_source']:r['original_tmp_source']['sha256']for r in prior['sources']};assert len(canonical)==10
for n,h in canonical.items():assert H(P(n))==h
records=[];seen=set()
for pair in prior['actual_paired_records']:
    record_p=checked(pair['actual_record']);record=J(record_p);log_p=checked(pair['raw_log']);snapshot=checked(pair['source_snapshot'])
    assert type(record['exit_code'])is int and record['exit_code']==0 and type(pair['actual_exit_code'])is int and pair['actual_exit_code']==0
    assert record['source']in canonical and pair['source']=={'file':record['source'],'sha256':canonical[record['source']]}
    assert record['source_sha256_before']==record['source_sha256_after']==H(snapshot)==canonical[record['source']]
    name=Path(record['source']).stem
    expected=['lake','env','lean','SafeLearning/'+name+'.lean']if pair['kind']=='standalone'else['lake','build','SafeLearning.'+name]
    assert record['command']==expected and record['actual_workdir']==str(R/'verification/lean')
    assert record['log']==pair['raw_log']['file']and record['log_sha256']==H(log_p)
    log_p.read_text();assert(pair['kind'],record['source'])not in seen;seen.add((pair['kind'],record['source']))
    records.append({'pair':pair,'entire_original_native_record':record})
assert seen=={(kind,n)for kind in ('standalone','named')for n in canonical}

# Real complete readonly helper invocation: no --apply, compiler or canonical writes.
log=Path('/tmp/root28-commissioning17-executor-readonly-independent-modules28-v1.log');assert not log.exists()
command=['python3',str(HELPER),'--plan',str(PLAN),'--plan-sha256',H(PLAN)]
with log.open('xb')as f:run=subprocess.run(command,cwd=R,stdout=f,stderr=subprocess.STDOUT)
assert run.returncode==0
ready=json.loads(log.read_text());assert ready=={'status':'ready_exact1_commissioning17_new_canonical_source_only','source_count':1,'public_theorems':17,'canonical_writes':0}
assert not P(row['canonical_source']).exists()

# Invoke the actual main/checked/guard code using only memory metadata mutations.
# The genuine reviewed context prefix runs once; its real held map is reused for fixtures.
spec=importlib.util.spec_from_file_location('modules_review_commissioning_executor',HELPER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
held=m.protection(source);realsha=m.sha;realloads=json.loads;fixtures=[]
prior_bytes=prior_p.read_bytes();actual_bytes=actual_p.read_bytes();plan_bytes=PLAN.read_bytes();peer_bytes=peer_p.read_bytes()
def reject(label,which=None,mutate=None,badsha=None):
    changes={};target={'prior':prior,'execution':actual,'plan':plan,'peer':peer}.get(which)
    if target is not None:
        fake=copy.deepcopy(target);mutate(fake);changes[{'prior':prior_bytes,'execution':actual_bytes,'plan':plan_bytes,'peer':peer_bytes}[which]]=fake
    def loads(raw,*args,**kwargs):return copy.deepcopy(changes[raw])if isinstance(raw,bytes)and raw in changes else realloads(raw,*args,**kwargs)
    m.json=types.SimpleNamespace(loads=loads,dumps=json.dumps)
    m.protection=lambda p:dict(held)
    m.sha=lambda p:('0'*64 if badsha is not None and Path(p)==badsha else realsha(p))
    previous=list(sys.argv);sys.argv=[str(HELPER),'--plan',str(PLAN),'--plan-sha256',H(PLAN)]
    try:
        try:m.main()
        except AssertionError:fixtures.append({'case':label,'rejected_by_actual_helper':True,'mode':'readonly_memory_fixture'})
        else:raise RuntimeError('negative accepted: '+label)
    finally:sys.argv=previous;m.sha=realsha
reject('prior completed status changed','prior',lambda d:d.update(status='pending'))
reject('prior errors inserted','prior',lambda d:d.update(errors=['bad']))
reject('prior declared source count changed','prior',lambda d:d.update(source_count=9))
reject('prior actual command count changed','prior',lambda d:d.update(actual_compiler_command_count=19))
reject('prior paired records pruned','prior',lambda d:d['actual_paired_records'].pop())
reject('prior paired exit boolean false','prior',lambda d:d['actual_paired_records'][0].update(actual_exit_code=False))
reject('prior paired exit nonzero','prior',lambda d:d['actual_paired_records'][0].update(actual_exit_code=1))
reject('prior outer exit boolean false','execution',lambda d:d.update(actual_exit_code=False))
reject('prior outer command changed','execution',lambda d:d['actual_command'].append('--invented'))
reject('prior outer cwd changed','execution',lambda d:d.update(actual_workdir='/tmp'))
reject('prior outer helper before-after disagreement','execution',lambda d:d['helper_sha256_after'].update({'book/coverage/checks/run_root28_current60_canonical_pairs_v2.py':'0'*64}))
reject('prior outer raw log hash changed','execution',lambda d:d.update(log_sha256='0'*64))
reject('prior native record hash changed','prior',lambda d:d['actual_paired_records'][0]['actual_record'].update(sha256='0'*64))
reject('prior snapshot hash changed','prior',lambda d:d['actual_paired_records'][0]['source_snapshot'].update(sha256='0'*64))
reject('prior paired raw log hash changed','prior',lambda d:d['actual_paired_records'][0]['raw_log'].update(sha256='0'*64))
reject('prior new canonical source byte guard mismatch',badsha=P(next(iter(canonical))))
reject('new source sourcecount wrong','plan',lambda d:d.update(source_count=2))
reject('new source declaration count wrong','plan',lambda d:d.update(public_theorem_count=18))
reject('new source overlaps selected Modules','plan',lambda d:d['sources'][0].update(canonical_source='verification/lean/SafeLearning/Modules.lean'))
reject('new source independent peer scope changed','peer',lambda d:d.update(status='pending'))
reject('new source independent peer source hash changed','peer',lambda d:d['source'].update(sha256='0'*64))
for n,h in canonical.items():assert H(P(n))==h
assert not m.BASE.exists()and not m.RESULT.exists()and not P(row['canonical_source']).exists()
result={'status':'passed_independent_commissioning17_canonical_executor_full_delta_and_readonly_guard_review','errors':[],'reader_started_at_utc':START,'reader_finished_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(HELPER),'helper_sha256':H(HELPER),'original_executor':ref(ORIGINAL),'author':ref(author),'plan':ref(PLAN),'exact_full_delta_reconstructed':True,'full_original_and_new_executor_and_author_read':True,'original_engine_body_retained_except13_counts_paths_status_replacements_and_prior_context_guard':True,'source':row['original_tmp_source'],'public_theorems':17,'independent_whole_peer':row['independent_whole_scope_peer'],'prior_completed_pairs':plan['prior_completed_pairs'],'prior_outer_execution':plan['prior_completed_pair_execution'],'prior_outer_raw_log':ref(priorlog),'entire_original_twenty_native_records':records,'held_ten_canonical_sources':canonical,'readonly_actual_command':command,'readonly_actual_exit_code':run.returncode,'readonly_raw_log':ref(log),'readonly_result':ready,'negative_fixtures':fixtures,'protected_original_context_counts':{'selected27_sources':1175,'assets60':31,'installed27_owners':5,'completed_new_canonical_sources':10,'completed_native_pairs':20},'new_actual_compiler_records_created_by_reviewer':0,'canonical_installation_or_owner_or_selection_or_publication_performed':False,'whole976_approved':False,'original_math_peer_bodies_and_times_reinterpreted':False,'coverage_complete':False,'scope':'Independent executor code/delta/actual readonly guard review only. Root may execute exact approved two-command batch afterward; final owner mapping and aggregate closure remain separate.'}
assert not OUT.exists();OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'reader':ref(OUT),'negative_fixtures':len(fixtures),'readonly_exit':0,'compiler_commands':0}))
