"""Install exact approved new sources and record real standalone/named builds.

Current60 assets, all1175 selected27 sources and five owner27 ledgers are held.
Owner installation, mathematical coverage, selection and aggregate audit follow.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, re, subprocess, sys

ROOT = Path('/home/oxrexkevin/SafetyBased')
BASE = ROOT/'book/coverage/checks/future28-core/current60-commissioning17-canonical-pair-v1'
RESULT = BASE/'actual-current60-commissioning17-canonical-paired-readiness28-v1.json'
RUNNER = Path('/tmp/root_tmp_lean28_source60_runner_v1.py')
RUNNER_SHA = 'f373a291a1f60cb15857935bf0b390adac8614f0d4226f5fc62ea6576a4fd18a'
HELPERS = {'standalone':('book/coverage/check_core_standalone.py','124bab45d3f48204b7436d721bf0b414c216a42e57b91a937dbd9e2ac6c8300a'),
           'named':('book/coverage/check_core_named_build.py','605ac2593a1b49044d011abc2d59cf3c4a422617929455754594199a5af73069')}

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def locate(n):
    p = Path(n)
    assert type(n) is str and n and str(p) == n and '..' not in p.parts
    if not p.is_absolute(): p = ROOT/p
    assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to('/tmp')
    assert p.is_file() and not p.is_symlink() and p.stat().st_size < 100_000_000
    return p
def checked(r):
    assert set(r) == {'file','sha256'} and re.fullmatch('[0-9a-f]{64}',r['sha256'])
    p = locate(r['file']); assert sha(p) == r['sha256']; return p
def zero(record):
    codes = [record[k] for k in ('actual_exit_code','exit_code','actual_runner_exit_code') if k in record]
    assert codes and all(type(c) is int and c == 0 for c in codes)
def new(p,data):
    assert not p.exists() and not p.is_symlink()
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('xb') as f: f.write(data)

def protection(source):
    assert sha(RUNNER) == RUNNER_SHA
    text = RUNNER.read_text(); marker = 'runner_before=sha(Path(__file__))\n'
    assert text.count(marker) == 1
    # Execute only the reviewed read-only prefix. No snapshot, command or
    # execution receipt is created by this original-context validation.
    namespace = {'__file__':str(RUNNER),'__name__':'root28_context_prefix'}
    prior = list(sys.argv)
    try:
        sys.argv = [str(RUNNER),str(source),'/tmp/root28-commissioning17-readonly-unused-v1.json']
        exec(compile(text.split(marker)[0],str(RUNNER),'exec'),namespace)
    finally: sys.argv = prior
    held = {**namespace['PINNED'],**namespace['held']}
    assert len(namespace['selection']['proof_files']) == 1175 and len(namespace['assets']) == 31 and len(namespace['owners']) == 5
    return held

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--plan',required=True)
    parser.add_argument('--plan-sha256',required=True)
    parser.add_argument('--apply',action='store_true')
    args = parser.parse_args()
    plan_p = checked({'file':args.plan,'sha256':args.plan_sha256})
    plan = json.loads(plan_p.read_bytes())
    assert plan['status'] == 'exact_reviewed_current60_commissioning17_canonical_pair_plan_only'
    rows = plan['sources']; assert len(rows) == plan['source_count'] == 1
    assert not BASE.exists() and not RESULT.exists()
    helper_sha = sha(Path(__file__))
    protected = protection(checked(rows[0]['original_tmp_source']))
    originals = {str(plan_p):sha(plan_p),str(RUNNER):RUNNER_SHA,str(Path(__file__)):helper_sha}
    # Hold the ten completed new modules and every native paired receipt too.
    prior_p = checked(plan['prior_completed_pairs']); prior = json.loads(prior_p.read_bytes())
    assert prior['status'] == 'passed_actual10_current60_canonical_standalone_and_named_pairs_unselected_future28'
    assert prior['errors'] == [] and prior['source_count'] == 10 and prior['actual_compiler_command_count'] == 20
    actual_p = checked(plan['prior_completed_pair_execution']); actual = json.loads(actual_p.read_bytes()); zero(actual)
    assert actual['actual_command'] == ['python3','book/coverage/checks/run_root28_current60_canonical_pairs_v2.py','--plan','/tmp/root28-current60-canonical-pair-plan-v1.json','--plan-sha256','64fe57b1296bf5d016eaf3da375a382454ea8c310c23c3421220000f0565533b','--apply']
    assert actual['actual_workdir'] == str(ROOT) and actual['helper_sha256_before'] == actual['helper_sha256_after']
    for n,h in actual['helper_sha256_after'].items(): originals[str(locate(n))] = h
    prior_log = checked({'file':actual['log'],'sha256':actual['log_sha256']})
    for p in [prior_p,actual_p,prior_log]: originals[str(p)] = sha(p)
    assert len(prior['actual_paired_records']) == 20
    for row in prior['sources']:
        p = locate(row['canonical_source']); assert sha(p) == row['original_tmp_source']['sha256']
        protected[row['canonical_source']] = sha(p)
    for row in prior['actual_paired_records']:
        assert type(row['actual_exit_code']) is int and row['actual_exit_code'] == 0
        for key in ('actual_record','raw_log','source_snapshot'):
            p = checked(row[key]); originals[str(p)] = sha(p)
    names, exported = set(), set()
    for row in rows:
        dest = Path(row['canonical_source']); name = dest.stem
        assert dest.as_posix() == row['canonical_source'] and dest.parent == Path('verification/lean/SafeLearning')
        assert name.startswith('Complete') and name.isidentifier() and dest.suffix == '.lean' and name not in names
        names.add(name); assert not (ROOT/dest).exists() and row['canonical_source'] not in protected
        source = checked(row['original_tmp_source'])
        assert source.is_relative_to('/tmp') and source.suffix == '.lean'
        declarations = re.findall(r'^(?:theorem|lemma)\s+([A-Za-z0-9_]+)',source.read_text(),re.M)
        assert len(declarations) == row['public_theorem_count'] and len(set(declarations)) == len(declarations)
        full_names = row['public_declarations']
        assert len(full_names) == len(declarations) and [n.rsplit('.',1)[1] for n in full_names] == declarations
        assert not exported.intersection(full_names); exported.update(full_names)
        peer_p = checked(row['independent_whole_scope_peer']); peer = json.loads(peer_p.read_bytes())
        assert peer['status'] == row['expected_peer_status'] and peer['errors'] == []
        semantic_source = peer.get('proof_source',peer.get('source'))
        assert {k:semantic_source[k] for k in ('file','sha256')} == row['original_tmp_source']
        original_p = checked(row['original_actual_tmp_trial']); trial = json.loads(original_p.read_bytes()); zero(trial)
        assert trial['actual_command'] == ['lake','env','lean',str(source)] and trial['actual_workdir'] == str(ROOT/'verification/lean')
        assert trial['source_sha256_before'] == trial['source_sha256_after'] == row['original_tmp_source']['sha256']
        log_p = checked({'file':trial['raw_log'],'sha256':trial['raw_log_sha256']})
        snapshot_p = checked({'file':trial['source_snapshot'],'sha256':trial['source_snapshot_sha256']})
        assert sha(snapshot_p) == sha(source)
        for p in [source,peer_p,original_p,log_p,snapshot_p]: originals[str(p)] = sha(p)
        for suffix in ['.log','-standalone.json','-named-build.log','-named-build.json']:
            assert not (ROOT/'book/coverage/checks'/(name+suffix)).exists()
    assert len(exported) == plan['public_theorem_count'] == 17
    for name,h in HELPERS.values(): assert sha(locate(name)) == h; protected[name] = h
    for r in plan['original_scope_plans']:
        p = checked(r); originals[str(p)] = sha(p)
    copied_canonical = False
    def guard():
        for n,h in protected.items(): assert sha(ROOT/n) == h,n
        assert sha(Path(__file__)) == helper_sha and sha(plan_p) == args.plan_sha256 and sha(RUNNER) == RUNNER_SHA
        for n,h in originals.items(): assert sha(locate(n)) == h,n
        if copied_canonical:
            for row in rows: assert sha(ROOT/row['canonical_source']) == row['original_tmp_source']['sha256']
    guard()
    if not args.apply:
        print(json.dumps({'status':'ready_exact1_commissioning17_new_canonical_source_only','source_count':1,'public_theorems':17,'canonical_writes':0})); return
    aliases, snapshots = {}, {}
    for original,h in originals.items():
        p = locate(original); target = BASE/'original-closed-bytes'/h/p.name
        if target.exists(): assert sha(target) == h
        else: new(target,p.read_bytes())
        assert sha(target) == h
        aliases[original] = {'file':target.relative_to(ROOT).as_posix(),'sha256':h}
    for row in rows:
        source = checked(row['original_tmp_source']); dest = ROOT/row['canonical_source']
        new(dest,source.read_bytes()); assert sha(dest) == sha(source)
        snapshot = BASE/'source-snapshots'/dest.name; new(snapshot,source.read_bytes())
        snapshots[row['canonical_source']] = {'file':snapshot.relative_to(ROOT).as_posix(),'sha256':sha(snapshot)}
    copied_canonical = True
    guard()
    pairs = []; environment = dict(os.environ); environment.pop('PYTHONHOME',None)
    for row in rows:
        name = Path(row['canonical_source']).stem
        for kind,suffix in [('standalone','-standalone.json'),('named','-named-build.json')]:
            guard()
            for other in rows: assert sha(ROOT/other['canonical_source']) == other['original_tmp_source']['sha256']
            child = ROOT/HELPERS[kind][0]
            invocation_log = BASE/(name+'-'+kind+'-helper-invocation.log')
            with invocation_log.open('xb') as f:
                result = subprocess.run([sys.executable,str(child),name],cwd=ROOT,env=environment,stdout=f,stderr=subprocess.STDOUT)
            guard()
            record_p = ROOT/'book/coverage/checks'/(name+suffix)
            record = json.loads(record_p.read_bytes())
            assert type(record['exit_code']) is int and record['exit_code'] == result.returncode
            assert record['source'] == row['canonical_source'] and record['source_sha256_before'] == record['source_sha256_after'] == row['original_tmp_source']['sha256']
            command = ['lake','env','lean','SafeLearning/'+name+'.lean'] if kind == 'standalone' else ['lake','build','SafeLearning.'+name]
            assert record['command'] == command and record['actual_workdir'] == str(ROOT/'verification/lean')
            checked({'file':record['log'],'sha256':record['log_sha256']})
            pairs.append({'kind':kind,'source':{'file':row['canonical_source'],'sha256':row['original_tmp_source']['sha256']},
                'actual_record':{'file':record_p.relative_to(ROOT).as_posix(),'sha256':sha(record_p)},'raw_log':{'file':record['log'],'sha256':record['log_sha256']},
                'source_snapshot':snapshots[row['canonical_source']],'actual_exit_code':record['exit_code']})
            print(json.dumps({'completed_actual_commands':len(pairs),'source':name,'kind':kind,'actual_exit_code':record['exit_code']}),flush=True)
            if result.returncode: raise SystemExit(result.returncode)
    guard(); assert len(pairs) == 2 and all(r['actual_exit_code'] == 0 for r in pairs)
    report = {'status':'passed_actual1_current60_commissioning17_canonical_standalone_and_named_pair_unselected_future28','errors':[],
              'completed_at_utc':datetime.now(timezone.utc).isoformat(),'source_count':1,'public_theorem_count':17,
              'actual_compiler_command_count':2,'sources':rows,'actual_paired_records':pairs,'source_snapshots':snapshots,
              'original_closed_byte_aliases':aliases,'protected_inputs_sha256':protected,'helper_sha256':helper_sha,
              'owner27_literal_identity_rebase_pending':True,'coverage_complete':False,'selection_or_aggregate_or_publication_claimed':False}
    new(RESULT,(json.dumps(report,indent=2)+'\n').encode())
    print(json.dumps({'status':'passed','readiness':RESULT.relative_to(ROOT).as_posix(),'sha256':sha(RESULT),'sources':1,'public_theorems':17,'actual_commands':2}))

if __name__ == '__main__': main()
