"""Install new reviewed bytes and execute real standalone and named Lean builds.

The supplied immutable context holds the prior audited sources, current lesson
bytes and five owners. This produces compiler evidence, not coverage decisions.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json, os, re, subprocess
ROOT=Path(__file__).resolve().parents[3]
HELPERS={'standalone':('book/coverage/check_core_standalone.py','124bab45d3f48204b7436d721bf0b414c216a42e57b91a937dbd9e2ac6c8300a'),
 'named':('book/coverage/check_core_named_build.py','605ac2593a1b49044d011abc2d59cf3c4a422617929455754594199a5af73069')}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def locate(n):
    assert type(n) is str and n and str(Path(n))==n and '..' not in Path(n).parts
    p=Path(n) if Path(n).is_absolute() else ROOT/n
    assert p.is_file() and not p.is_symlink() and p.stat().st_size<100_000_000
    assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to('/tmp')
    return p
def checked(r):
    assert re.fullmatch('[0-9a-f]{64}',r['sha256']);p=locate(r['file']);assert sha(p)==r['sha256'];return p
def zero(d):
    codes=[d[k] for k in ['actual_exit_code','exit_code','actual_runner_exit_code'] if k in d]
    assert codes and all(type(v) is int and v==0 for v in codes)
    assert d.get('protection_errors',[])==[]
def new(p,data):
    assert p.resolve().is_relative_to(ROOT.resolve())
    assert all(not q.is_symlink() for q in [p,*p.parents] if q.is_relative_to(ROOT))
    assert not p.exists() and not p.is_symlink();p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('xb') as f:f.write(data)
def contains_sha(d,h):
    if isinstance(d,dict):return d.get('sha256')==h or any(contains_sha(v,h) for v in d.values())
    if isinstance(d,list):return any(contains_sha(v,h) for v in d)
    return d==h

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--plan',required=True);ap.add_argument('--plan-sha256',required=True);ap.add_argument('--apply',action='store_true');args=ap.parse_args()
    plan_p=checked({'file':args.plan,'sha256':args.plan_sha256});plan=json.loads(plan_p.read_bytes())
    assert plan['status']=='exact_reviewed_new_canonical_pair_plan30_only'
    base=Path(plan['result_directory']);assert not base.is_absolute() and '..' not in base.parts and base.parts[:4]==('book','coverage','checks','future30-core')
    base=ROOT/base;assert not base.exists() and base.resolve().is_relative_to(ROOT.resolve())
    assert all(not q.is_symlink() for q in [base,*base.parents] if q.is_relative_to(ROOT))
    context_p=checked(plan['context']);context=json.loads(context_p.read_bytes())
    assert context['coverage_complete'] is False and len(context['owners_sha256'])==5
    assert context['status']=='current_source79_with_unchanged_historical_source65_owner29_for_tmp_trials_only'
    assert context['owner_identity_rebase_pending'] is True and context['aggregate_source79_verification_claimed'] is False
    audit=json.loads(checked(context['actual_audit']).read_bytes());assert audit['status']=='passed' and audit['proof_file_count']==1197
    protected={**context['pins_sha256'],**context['held_current_source_sha256']}
    assert all(protected[n]==h for n,h in audit['proof_sha256'].items())
    assert sum(n.startswith('SafeLearning/') for n in protected)==31
    for n,h in context['owners_sha256'].items():assert protected[n]==h
    originals={str(context_p):sha(context_p),str(plan_p):sha(plan_p),str(Path(__file__)):sha(Path(__file__))}
    for n,h in HELPERS.values():assert sha(locate(n))==h;protected[n]=h
    spec=importlib.util.spec_from_file_location('root30_canonical_names',ROOT/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
    assert sha(ROOT/'book/coverage/lean_names.py')==protected['book/coverage/lean_names.py']
    selected_names={r['name'] for n in audit['proof_sha256'] for r in names.declarations(locate(n).read_text())}
    rows=plan['sources'];assert len(rows)==plan['source_count'] and rows
    all_new_names=set();destinations=set()
    for r in rows:
        dest=Path(r['canonical_source']);assert dest.parent==Path('verification/lean/SafeLearning') and dest.suffix=='.lean' and dest.stem.startswith('Complete') and dest.stem.isidentifier()
        assert str(dest) not in destinations and not (ROOT/dest).exists();destinations.add(str(dest))
        source=checked(r['original_tmp_source']);assert source.suffix=='.lean'
        declarations=names.declarations(source.read_text());assert declarations==r['public_declarations']
        theorem_count=sum(v['kind'] in ['theorem','lemma'] for v in declarations);assert theorem_count==r['public_theorem_count']
        public_names={v['name'] for v in declarations};assert len(public_names)==len(declarations)
        assert not public_names.intersection(selected_names|all_new_names);all_new_names.update(public_names)
        assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',names.without_comments(source.read_text()))
        trial_p=checked(r['original_actual_tmp_trial']);trial=json.loads(trial_p.read_bytes());zero(trial)
        assert trial['actual_command']==['lake','env','lean',trial['source']] and trial['actual_workdir']==str(ROOT/'verification/lean')
        assert trial['source_sha256_before']==trial['source_sha256_after']==trial['source_snapshot_sha256']==sha(source)
        snapshot=checked({'file':trial['source_snapshot'],'sha256':trial['source_snapshot_sha256']})
        log=checked({'file':trial['raw_log'],'sha256':trial['raw_log_sha256']})
        peers=r['independent_source_peers'];assert peers
        assert any(contains_sha(json.loads(checked(pr).read_bytes()),sha(source)) for pr in peers)
        for pr in peers:
            pp=checked(pr);peer=json.loads(pp.read_bytes());assert peer['status'].startswith('passed_')
            if 'errors' in peer:
                assert peer['errors']==[]
            else:
                assert pr['sha256']=='1f5d55ccde76a5dd98bb497ca4c120af9c0e29324de0efc4c5e784d5e99c209d'
                assert peer['status']=='passed_independent_full15_prospective_corrected_norm190_semantic_review'
                assert peer['actual_checker_exit_code']==0 and peer['protection_errors']==[]
                assert peer['prospective_corrected190_whole_semantic_approved'] is True
                assert peer['current190_whole_approved'] is False
            originals[str(pp)]=sha(pp)
        for pp in [source,trial_p,snapshot,log]:originals[str(pp)]=sha(pp)
        for suffix in ['.log','-standalone.json','-named-build.log','-named-build.json']:
            assert not (ROOT/'book/coverage/checks'/(dest.stem+suffix)).exists()
    assert sum(r['public_theorem_count'] for r in rows)==plan['public_theorem_count']
    installed=False
    def guard():
        for n,h in protected.items():assert sha(locate(n))==h,n
        for n,h in originals.items():assert sha(locate(n))==h,n
        if installed:
            for r in rows:assert sha(locate(r['canonical_source']))==r['original_tmp_source']['sha256']
    guard()
    if not args.apply:
        print(json.dumps({'status':'ready_exact_reviewed30_canonical_pair_batch','sources':len(rows),'public_names':len(all_new_names),'theorem_lemma_count':plan['public_theorem_count'],'canonical_writes':0}));return
    aliases={};snapshots={}
    for n,h in originals.items():
        pp=locate(n);target=base/'original-closed-bytes'/h/pp.name
        if target.exists():assert sha(target)==h
        else:new(target,pp.read_bytes())
        aliases[n]={'file':target.relative_to(ROOT).as_posix(),'sha256':h}
    for r in rows:
        source=checked(r['original_tmp_source']);dest=ROOT/r['canonical_source'];new(dest,source.read_bytes())
        snapshot=base/'source-snapshots'/dest.name;new(snapshot,source.read_bytes())
        snapshots[r['canonical_source']]={'file':snapshot.relative_to(ROOT).as_posix(),'sha256':sha(snapshot)}
    installed=True;guard();pairs=[];environment=dict(os.environ);environment.pop('PYTHONHOME',None)
    for r in rows:
        name=Path(r['canonical_source']).stem
        for kind,suffix in [('standalone','-standalone.json'),('named','-named-build.json')]:
            guard();helper=ROOT/HELPERS[kind][0]
            with (base/(name+'-'+kind+'-helper-invocation.log')).open('xb') as f:
                result=subprocess.run(['python3',str(helper),name],cwd=ROOT,env=environment,stdout=f,stderr=subprocess.STDOUT)
            guard();record_p=ROOT/'book/coverage/checks'/(name+suffix);record=json.loads(record_p.read_bytes())
            assert type(record['exit_code']) is int and record['exit_code']==result.returncode
            assert record['source']==r['canonical_source'] and record['source_sha256_before']==record['source_sha256_after']==r['original_tmp_source']['sha256']
            command=['lake','env','lean','SafeLearning/'+name+'.lean'] if kind=='standalone' else ['lake','build','SafeLearning.'+name]
            assert record['command']==command and record['actual_workdir']==str(ROOT/'verification/lean')
            checked({'file':record['log'],'sha256':record['log_sha256']})
            pairs.append({'kind':kind,'source':{'file':r['canonical_source'],'sha256':r['original_tmp_source']['sha256']},'actual_record':{'file':record_p.relative_to(ROOT).as_posix(),'sha256':sha(record_p)},'raw_log':{'file':record['log'],'sha256':record['log_sha256']},'source_snapshot':snapshots[r['canonical_source']],'actual_exit_code':record['exit_code']})
            print(json.dumps({'completed_actual_commands':len(pairs),'source':name,'kind':kind,'actual_exit_code':record['exit_code']}),flush=True)
            if result.returncode:raise SystemExit(result.returncode)
    guard();assert len(pairs)==2*len(rows) and all(r['actual_exit_code']==0 for r in pairs)
    report={'status':'passed_actual_reviewed30_canonical_standalone_and_named_pairs_unselected','errors':[],'completed_at_utc':datetime.now(timezone.utc).isoformat(),'source_count':len(rows),'public_theorem_count':plan['public_theorem_count'],'public_name_count':len(all_new_names),'actual_compiler_command_count':len(pairs),'sources':rows,'actual_paired_records':pairs,'source_snapshots':snapshots,'original_closed_byte_aliases':aliases,'protected_inputs_sha256':protected,'context':plan['context'],'coverage_complete':False,'selection_aggregate_owner_or_publication_claimed':False}
    target=base/'actual-reviewed30-canonical-paired-readiness-v1.json';new(target,(json.dumps(report,indent=2)+'\n').encode())
    print(json.dumps({'status':report['status'],'readiness':{'file':target.relative_to(ROOT).as_posix(),'sha256':sha(target)},'sources':len(rows),'actual_commands':len(pairs),'coverage_complete':False}))

if __name__=='__main__':main()
