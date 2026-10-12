from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json

ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p): return {'file':str(p),'sha256':sha(p)}
def encode(j): return (json.dumps(j,indent=2)+'\n').encode()
def native_peer(p,expected):
    assert sha(p)==expected
    j=json.loads(p.read_bytes()); assert j['errors']==[]
    for k in ('actual_checker','original_findings','actual_reader_execution','actual_reader_raw_log','actual_reader_runner'):
        r=j[k]; assert sha(r['file'])==r['sha256'],k
    original=json.loads(Path(j['original_findings']['file']).read_bytes())
    assert j['entire_original_findings_body_and_time']==original
    for k,v in original.items(): assert j[k]==v or k=='closed_evidence_sha256',k
    actual=json.loads(Path(j['actual_reader_execution']['file']).read_bytes())
    assert type(actual['actual_exit_code']) is int and actual['actual_exit_code']==0
    assert actual['actual_command']==['python3',j['actual_checker']['file']]
    assert actual['actual_workdir']==str(ROOT)
    assert actual['checker_sha256_before']==actual['checker_sha256_after']==j['actual_checker']['sha256']
    assert actual['actual_runner']==j['actual_reader_runner']
    assert actual['raw_log']==j['actual_reader_raw_log']['file']
    assert actual['raw_log_sha256']==j['actual_reader_raw_log']['sha256']
    assert actual['started_at_utc'] < actual['finished_at_utc'] and actual['elapsed_seconds']>0
    logged=json.loads(Path(actual['raw_log']).read_bytes())
    assert logged['findings']==j['original_findings']
    for n,h in j['closed_evidence_sha256'].items(): assert sha(n)==h,n
    return j

def archive(paths,base,scope):
    base=ROOT/base; assert not base.exists()
    aliases={}
    for p in paths:
        p=Path(p); b=p.read_bytes(); h=sha(p); target=base/h/p.name
        target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('xb') as f:f.write(b)
        assert target.read_bytes()==b and sha(target)==h
        aliases[str(p)]={'file':str(target.relative_to(ROOT)),'sha256':h}
    catalog=base/'original-closed-byte-aliases-v1.json'
    body={'status':'closed_exact_original_byte_aliases','archived_at_utc':datetime.now(timezone.utc).isoformat(),'original_file_count':len(aliases),'original_closed_byte_aliases':aliases,'scope':scope}
    with catalog.open('xb') as f:f.write(encode(body))
    return ref(catalog),aliases

dp=Path('/tmp/delivery27-helper5-independent-modules-review-v1.json')
d=native_peer(dp,'3cd4c3bbfc991301dbc3df37f0628a383441273329d9889234e156f49c7d02f9')
assert d['status']=='passed_independent_full_delivery27_helper_review'
assert d['fixture_count']==len(d['fixture_observations'])==42
assert all(x['synthetic'] is True and x['observed']==x['expected'] for x in d['fixture_observations'])
assert d['future_actual_delivery_positive_execution_is_pending'] is True
helper=Path('/tmp/root_close_publication27_delivery_v5.py')
assert d['full_helper_body']==helper.read_text() and sha(helper)==d['helper_sha256']
assert d['entire_original_helper4_body']==Path('/tmp/root_close_publication27_delivery_v4.py').read_text()
assert [x['entire_original_body_and_time']['actual_exit_code'] for x in d['author_native_prefix_execution_histories_unchanged']]==[1,1,0,0]
for item in d['author_native_prefix_execution_histories_unchanged']:
    r=item['actual_execution']; assert sha(r['file'])==r['sha256']
    assert json.loads(Path(r['file']).read_bytes())==item['entire_original_body_and_time']
prefix=Path('/tmp/delivery27-helper5-native-prefix-actual-v1.json'); a=json.loads(prefix.read_bytes())
assert type(a['actual_exit_code'])is int and a['actual_exit_code']==0
assert a['actual_command']==['python3','/tmp/check-delivery27-helper5-native-prefix-v1.py']
assert a['actual_workdir']==str(ROOT) and sha(a['raw_log'])==a['raw_log_sha256']
for n,h in a['helper_sha256_before'].items():assert sha(n)==h==a['helper_sha256_after'][n]
assert sha(a['actual_runner']['file'])==a['actual_runner']['sha256']
delivery_paths=[helper,dp,*[Path(d[k]['file']) for k in ('actual_checker','original_findings','actual_reader_execution','actual_reader_raw_log','actual_reader_runner')],prefix,Path(a['raw_log']),Path(a['actual_runner']['file']),Path('/tmp/check-delivery27-helper5-native-prefix-v1.py'),Path('/tmp/delivery27-helper5-native-prefix-findings-v1.json')]
dc,da=archive(delivery_paths,'book/coverage/checks/future27-core/original-delivery27-foundations-helper5-and-independent-peer-v1','Exact original helper5, genuine current immutable-prefix execution and independent 42 isolated synthetic guard observations; retain the original failed helper2/3 and passed helper4/5 bodies/times. No successful future production delivery, updater or Git staging is claimed by this archive.')
binding=copy.deepcopy(d)
binding['actual_reader_execution']=da[d['actual_reader_execution']['file']]
binding['original_independent_code_review']=da[str(dp)]
binding['entire_original_independent_code_review_body_and_time']=d
binding['canonical_byte_binding']={'status':'exact_original_reader_bytes_bound_to_relative_metadata_alias','bound_at_utc':datetime.now(timezone.utc).isoformat(),'original_archive_catalog':dc,'only_original_review_field_rebound':'actual_reader_execution','new_review_or_execution_claimed':False,'production_delivery_positive_still_pending':True}
unchanged=copy.deepcopy(binding)
for k in ('original_independent_code_review','entire_original_independent_code_review_body_and_time','canonical_byte_binding'):unchanged.pop(k)
unchanged['actual_reader_execution']=d['actual_reader_execution'];assert unchanged==d
bp=ROOT/'book/coverage/checks/delivery27-helper5-independent-modules-byte-binding-v1.json'
assert not bp.exists()
with bp.open('xb') as f:f.write(encode(binding))
assert sha(ROOT/binding['actual_reader_execution']['file'])==binding['actual_reader_execution']['sha256']

gp=Path('/tmp/foundations-literal-gradient15-independent-modules-full-source-review28-v1.json')
g=native_peer(gp,'f6eb36bc6e27e4b93f365fbadfd3b877c61a3afdfe9e5c660c83b387482766d8')
assert g['public_theorem_count']==15 and g['actual_warning_count']==1
assert [u['source_unit_key'] for u in g['material_units']]==['primer-optimization.html::node-178','primer-optimization.html::node-208','primer-optimization.html::node-210']
assert all(u['whole_unit_approved'] is True and u['missing_clauses']==[] and u['remaining_gaps']==[] for u in g['material_units'])
assert g['entire_source']==Path(g['proof_source']['file']).read_text()
gc,ga=archive([gp,*[Path(g[k]['file'])for k in ('actual_checker','original_findings','actual_reader_execution','actual_reader_raw_log','actual_reader_runner')]],'book/coverage/checks/future28-foundations/original-literal-gradient15-independent-modules-review28-v1','Exact original independent full-source semantic approval of all three complete literal units178/208/210. Current1175/31/five before/after closure is checked; original compiler failures1/2 and success3, one warning, full source bodies and review times are retained without alteration. No canonical proof, owner, source or mapping installation is performed.')
print(json.dumps({'delivery_original_catalog':dc,'delivery_peer_byte_binding':ref(bp),'delivery_peer_native_fixture_count':42,'gradient15_original_peer_catalog':gc,'gradient15_whole_units_approved':3,'current_closed_delivery_refs':len(d['closed_evidence_sha256']),'current_closed_gradient_refs':len(g['closed_evidence_sha256'])}))
