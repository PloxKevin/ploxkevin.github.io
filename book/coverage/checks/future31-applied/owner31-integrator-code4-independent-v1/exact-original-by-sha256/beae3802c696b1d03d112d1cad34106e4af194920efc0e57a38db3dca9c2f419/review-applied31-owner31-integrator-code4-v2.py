from pathlib import Path
from datetime import datetime, timezone
import sys, json, hashlib, importlib.util, tempfile, time, traceback
sys.dont_write_bytecode = True
ROOT=Path('/home/oxrexkevin/SafetyBased')
SELF=Path(__file__)
TARGET='book/coverage/checks/root_integrate_owner31_candidates_v4.py'
BINDING='book/coverage/checks/future31-core/owner31-exact-reviewed-bindings-v1.json'
TARGET_SHA='7e5ec0e31e7b639aa93ceca986a965140581c6827202913ea5ed5c7ebd034b3e'
BINDING_SHA='97ea41899a0d32c89bbb9f5a3820c95b044112a52c06c01d3a1ccada13d3ecb6'
OUT=Path('/tmp/applied31-owner31-integrator-code4-review-v2')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):
    q=Path(p); q=q if q.is_absolute() else ROOT/q
    return {'file':str(q), 'sha256':digest(q), 'bytes':q.stat().st_size}
def load_module(name,p):
    spec=importlib.util.spec_from_file_location(name,p)
    mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
def guard(table):
    for name,h in table.items():
        p=Path(name); p=p if p.is_absolute() else ROOT/p
        assert digest(p)==h,name
def write(p,d):
    with p.open('xb') as f: f.write((json.dumps(d,indent=2)+'\n').encode())
assert not OUT.exists(); OUT.mkdir()
start=datetime.now(timezone.utc); clock=time.monotonic(); helper_before=digest(SELF)
errors=[]; before={}; assessment={}
try:
    assert digest(ROOT/TARGET)==TARGET_SHA
    assert digest(ROOT/BINDING)==BINDING_SHA
    m=load_module('integration_code4_read_only',ROOT/TARGET)
    # Import only: the producer main function is never called by this reader.
    text=(ROOT/TARGET).read_text(); assert text.endswith("if __name__ == '__main__': main()\n")
    assert len(text.splitlines())==179
    c=json.loads(m.CONTEXT.read_bytes()); assert digest(m.CONTEXT)==m.CONTEXT_SHA
    before={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}
    assert not set(c['owners_sha256']) & set(c['pins_sha256'])
    s=m.read(m.SELECTION); ready=m.read(m.READINESS); native=m.read(m.NATIVE)
    assert m.sha(m.SELECTION)==m.SELECTION_SHA and m.sha(m.READINESS)==m.READINESS_SHA
    assert m.sha('book/coverage/inventory.json')==m.INVENTORY_SHA
    before[TARGET]=TARGET_SHA;before[BINDING]=BINDING_SHA
    before[m.SELECTION]=m.SELECTION_SHA;before[m.READINESS]=m.READINESS_SHA;before[m.NATIVE]=m.sha(m.NATIVE)
    before['book/coverage/validate.py']=m.sha('book/coverage/validate.py')
    before[str(m.CONTEXT)]=m.CONTEXT_SHA
    for name,r in s['proof_files'].items(): before[name]=r['sha256']
    guard(before)
    assert s['proof_file_count']==len(s['proof_files'])==1248
    assert ready['status'].startswith('passed') and ready['errors']==[]
    assert ready['source_count']==len(ready['sources'])==6
    assert ready['public_theorem_count']==sum(r['public_theorem_count'] for r in ready['sources'])==104
    assert ready['actual_compiler_command_count']==len(ready['actual_paired_records'])==12
    assert {r['canonical_source'] for r in ready['sources']}==set(m.NEW_OWNERS)
    m.zero(native); assert native['status']=='passed'
    assert native['helper_sha256_before']==native['helper_sha256_after']
    assert m.sha(native['log'])==native['log_sha256']
    assert s['actual_new6_compiler_execution']['sha256']==m.sha(m.NATIVE)
    paired=[]
    for pair in ready['actual_paired_records']:
        record=m.checked(pair['actual_record'])
        for key in ['source','raw_log','source_snapshot']: m.checked(pair[key],False)
        h=pair['source']['sha256']; n=pair['source']['file']
        assert s['proof_files'][n]['sha256']==h==pair['source_snapshot']['sha256']
        assert record['source_sha256_before']==record['source_sha256_after']==h
        assert record['source_unchanged'] is True and record['exit_code']==0 and record['status']=='passed'
        assert record['log']==pair['raw_log']['file'] and record['log_sha256']==pair['raw_log']['sha256']
        assert record['actual_workdir']==str(ROOT/'verification/lean')
        expected=['lake','env','lean',n.removeprefix('verification/lean/')] if pair['kind']=='standalone' else ['lake','build',n.removeprefix('verification/lean/').removesuffix('.lean').replace('/','.')]
        assert record['command']==expected
        paired.append({'source':n,'kind':pair['kind'],'actual_record':pair['actual_record'],'source_sha256':h})
    assert {(p['source'],p['kind']) for p in paired}=={(n,k) for n in m.NEW_OWNERS for k in ['standalone','named']}
    b=m.checked({'file':BINDING,'sha256':BINDING_SHA}); rows=b['replacements']
    assert b['status']=='exact_source81_five_owner31_reviewed_candidate_byte_bindings_only'
    assert len(rows)==5 and {r['destination'] for r in rows}==set(c['owners_sha256'])
    nativechecks=[];proofchecks=[]; normalized={};oldaliases={}
    for r in rows:
        dest=r['destination']; owner=Path(dest).stem
        assert r['before_sha256']==c['owners_sha256'][dest]==m.sha(dest)
        candidate=m.checked(r['candidate']); a=m.checked(r['independent_mapping_peer'])
        assert a['status']==r['expected_peer_status'] and a['errors']==[]
        assert m.pointer(a,r['peer_candidate_pointer'])==r['candidate']
        assert r['required_true_peer_fields'] and all(m.pointer(a,k) is True for k in r['required_true_peer_fields'])
        aliases={};schemas={}
        for key in ['all_original_byte_aliases','actual_reader_original_byte_aliases','actual_finalizer_original_byte_aliases']:
            table=a.get(key,{}); assert isinstance(table,dict);schemas[key]=len(table)
            for original,alias in table.items():
                v=m.normalize_alias(original,alias)
                if original in aliases: assert (aliases[original]['sha256'],aliases[original]['bytes'])==(v['sha256'],v['bytes'])
                else: aliases[original]=v
        n=m.success_native(a['actual_reader'],aliases)
        nativechecks.append({'destination':dest,'peer':r['independent_mapping_peer'],'reader':a['actual_reader'],'schemas':schemas,'native_status':n['status'],'actual_exit_code':n.get('actual_exit_code')})
        normalized[dest]=aliases
        oldalias=a.get('exact_original_mutable_owner_to_existing_immutable_whole_byte_aliases',{}).get(dest,a.get('original_whole_owner30'))
        assert oldalias is not None and oldalias['sha256']==r['before_sha256'];m.checked(oldalias,False);oldaliases[dest]=oldalias
        before[r['candidate']['file']]=r['candidate']['sha256'];before[r['independent_mapping_peer']['file']]=r['independent_mapping_peer']['sha256']
        before[a['actual_reader']['file']]=a['actual_reader']['sha256']
        for alias in aliases.values():before[alias['file']]=alias['sha256']
        if owner!='applied-promotions':
            old=m.read(dest); oldproof=m.proof_hashes(old);newproof=m.proof_hashes(candidate)
            additions={n:s['proof_files'][n]['sha256'] for n,o in m.NEW_OWNERS.items() if o==owner}
            assert newproof=={**oldproof,**additions}
            if isinstance(old['proof_files'],dict): assert all(candidate['proof_files'][n]==v for n,v in old['proof_files'].items())
            else: assert candidate['proof_files'][:len(old['proof_files'])]==old['proof_files']
            for n,h in newproof.items():assert m.sha(n)==h
            proofchecks.append({'owner':owner,'old_proof_count':len(oldproof),'new_proof_count':len(newproof),'only_additions':additions,'all_old_proof_metadata_unchanged':True})
    guard(before)
    with tempfile.TemporaryDirectory(prefix='independent-owner31-code4-isolated-') as tmp:
        t=Path(tmp);(t/'book/coverage').mkdir(parents=True);(t/'verification').mkdir()
        (t/'SafeLearning').symlink_to(ROOT/'SafeLearning',target_is_directory=True)
        (t/'verification/lean').symlink_to(ROOT/'verification/lean',target_is_directory=True)
        (t/'book/coverage/inventory.json').symlink_to(ROOT/'book/coverage/inventory.json')
        for r in rows:(t/r['destination']).symlink_to(ROOT/r['candidate']['file'])
        sys.path.insert(0,str(ROOT/'book/coverage'))
        validator=load_module('independent_owner31_code4_validator',ROOT/'book/coverage/validate.py');validator.ROOT=t
        report=validator.validate()
    guard(before)
    assert report['integrity_status']=='passed' and report['errors']==[] and report['mathematical_coverage_complete'] is False
    assert report['counts']['exercises']==556 and report['counts']['material_source_units']==12774
    write(OUT/'independent-isolated-validator.json',report)
    assessment={'full_code_read':True,'reviewed_helper':m.ref(TARGET),'exact_binding':m.ref(BINDING),'three_distinct_peers':len({r['independent_mapping_peer']['sha256'] for r in rows}),'all_five_candidate_peer_references_and_required_true_fields_match':True,'real_six_sources_twelve_pairs':paired,'peer_reader_schema_checks':nativechecks,'proof_metadata_checks':proofchecks,'normalized_aliases_by_destination':normalized,'old_five_whole_byte_aliases':oldaliases,'independent_isolated_validator':ref(OUT/'independent-isolated-validator.json'),'counts':report['counts'],'default_and_apply_paths_reviewed':True,'source_and_selected1248_guards_unchanged':True,'raw_owner_write_by_reviewer':False,'producer_executed_by_reviewer':False,'coverage_complete':False,'scope':'Exact v4 helper with binding97ea and three actual peers only. The isolated validator covers four domain ledgers; the promotions mirror is separately bound to the complete independent Core/Applied/promotions peer. The producer archives old five bytes before writes, checks each installed candidate, and guards source/proof/immutable inputs afterward. No installation, fresh compiler, aggregate kernel, axiom or publication claim is made.'}
except Exception as exc:
    errors.append(type(exc).__name__+': '+str(exc));traceback.print_exc()
finish=datetime.now(timezone.utc); elapsed=time.monotonic()-clock
write(OUT/'assessment.json',{**assessment,'status':'passed_exact_owner31_integrator_code4_independent_read_only_review' if not errors else 'failed_owner31_integrator_code4_independent_read_only_review','errors':errors})
write(OUT/'actual-reader.json',{'status':'passed' if not errors else 'failed','actual_command':['python3',str(SELF)],'actual_workdir':str(ROOT),'actual_exit_code':0 if not errors else 1,'started_at_utc':start.isoformat(),'finished_at_utc':finish.isoformat(),'elapsed_seconds':elapsed,'helper_sha256_before':{str(SELF):helper_before},'helper_sha256_after':{str(SELF):digest(SELF)},'protected_inputs_sha256_before':before,'protected_inputs_sha256_after':{n:digest(Path(n) if Path(n).is_absolute() else ROOT/n) for n in before},'protection_errors':[] if not errors else errors,'scope':'Actual independent read-only byte/schema/proof-map and isolated-validator execution, not producer or Lean compiler.'})
print(json.dumps({'status':'passed' if not errors else 'failed','errors':errors,'assessment':ref(OUT/'assessment.json'),'actual_reader':ref(OUT/'actual-reader.json'),'elapsed_seconds':elapsed}))
sys.exit(0 if not errors else 1)
