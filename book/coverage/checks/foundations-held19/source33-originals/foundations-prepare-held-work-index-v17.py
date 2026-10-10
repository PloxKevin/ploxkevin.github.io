import copy, datetime, hashlib, json, pathlib, re

R=pathlib.Path('/home/oxrexkevin/SafetyBased')
def P(p):
    q=pathlib.Path(p)
    return q if q.is_absolute() else R/q
def H(p): return hashlib.sha256(P(p).read_bytes()).hexdigest()

prior='/tmp/foundations-future19-held-work-index-v16.json'
assert H(prior)=='1f5b7dff276f062bee55a9de427aff0b0eb8838d819c1ea9513eefc73aba9900'
old=json.loads(P(prior).read_text());out=copy.deepcopy(old)
for p,h in old['held_current_metadata_sha256'].items():assert H(p)==h

new_records=[
    '/tmp/foundations-supremum-lesson-trial3.json',
    '/tmp/foundations-supremum-examples-trial4.json',
    '/tmp/foundations-extended-real-values-trial1.json',
    '/tmp/foundations-maximum-existence-trial1.json',
    '/tmp/foundations-safeopt-extended-bands-trial2.json',
    '/tmp/foundations-extended-supremum-rules-trial2.json',
    '/tmp/foundations-liminf-limsup-lesson-trial3.json',
    '/tmp/foundations-supremum-proof-routes-trial2.json']
for p in new_records:
    r=json.loads(P(p).read_text())
    assert r['exit_code']==0 and r['source_unchanged']
    assert H(r['source'])==r['source_sha256_before']==r['source_sha256_after']==H(r['preserved_source'])==r['preserved_source_sha256']
    assert H(r['log'])==r['log_sha256']
    t=P(r['source']).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',t)
    assert r['source'] not in {x['file'] for x in out['actual_new_unselected_proof_records']}
    out['actual_new_unselected_proof_records'].append(dict(file=r['source'],sha256=H(r['source']),
        actual_standalone_evidence=p,actual_standalone_evidence_sha256=H(p),actual_exit_code=0,
        log=r['log'],log_sha256=r['log_sha256'],raw_log_empty=not P(r['log']).read_bytes(),
        declared_theorems=re.findall(r'^theorem\s+(\w+)',t,re.M),imports=re.findall(r'^import\s+(.+)$',t,re.M),
        preserved_source=r['preserved_source'],preserved_source_sha256=r['preserved_source_sha256']))
assert sum(len(x['declared_theorems']) for x in out['actual_new_unselected_proof_records'][-8:])==69

failed=[f'/tmp/foundations-supremum-lesson-trial{i}.json' for i in [1,2]]+[
    f'/tmp/foundations-supremum-examples-trial{i}.json' for i in [1,2,3]]+[
    '/tmp/foundations-safeopt-extended-bands-trial1.json',
    '/tmp/foundations-extended-supremum-rules-trial1.json']+[
    f'/tmp/foundations-liminf-limsup-lesson-trial{i}.json' for i in [1,2]]+['/tmp/foundations-supremum-proof-routes-trial1.json']
for p in failed:
    r=json.loads(P(p).read_text())
    assert r['exit_code']==1 and r['source_unchanged']
    assert r['source_sha256_before']==r['source_sha256_after']==H(r['preserved_source'])==r['preserved_source_sha256']
    assert H(r['log'])==r['log_sha256']
    assert p not in {x['file'] for x in out['failed_execution_history']}
    out['failed_execution_history'].append(dict(file=p,sha256=H(p),source_snapshot=r['preserved_source'],
        source_snapshot_sha256=r['preserved_source_sha256'],log=r['log'],log_sha256=r['log_sha256'],
        actual_exit_code=1,original_execution_record=r))

named='/tmp/foundations-extended-real-values-named-actual1.json';r=json.loads(P(named).read_text())
assert r['exit_code']==0 and r['source_unchanged']
assert H(r['source'])==r['source_sha256_before']==r['source_sha256_after']==H(r['preserved_source'])==r['preserved_source_sha256']
assert H(r['log'])==r['log_sha256']
out['new_actual_named_dependency_evidence'].append(dict(file=named,sha256=H(named),actual_exit_code=0,
    source=r['source'],source_sha256=H(r['source']),log=r['log'],log_sha256=r['log_sha256'],
    original_execution_record=r,limits='Sole genuine named dependency build of immutable ExtendedRealValues; log has actual build-success lines and is nonempty. No second source counted.'))

def review(p):
    d=json.loads(P(p).read_text())
    sm=d['source_sha256'];sm={d['source']:sm} if isinstance(sm,str) else sm
    for s,h in sm.items():assert H(s)==h
    for s,h in d.get('proof_source_sha256',{}).items():assert H(s)==h
    for e in d.get('actual_standalone_evidence',[])+d.get('named_build_evidence',[]):
        assert H(e['compiler_manifest'])==e['compiler_manifest_sha256']
        rr=json.loads(P(e['compiler_manifest']).read_text())
        stored=e.get('raw_execution_record',e.get('record'))
        assert rr==stored or stored in rr.get('files',[])
        for raw in rr.get('files',[rr]):
            assert raw['exit_code']==0 and H(raw['log'])==raw['log_sha256']
            assert H(raw.get('source',raw.get('file')))==raw.get('source_sha256_after',raw.get('sha256_after',raw.get('sha256')))
    return dict(file=p,sha256=H(p),status=d['status'],reviewer=d.get('reviewer'),
        reviewed_at_utc=d.get('reviewed_at_utc'),supplement_reviewed_at_utc=d.get('supplement_reviewed_at_utc'),
        missing_clauses=d.get('missing_clauses',[]))

new_reviews = [
    '/tmp/foundations-supremum-material-source-components-review19-v1.json',
    '/tmp/foundations-supremum-material-source-components-review19-v2-proof-routes.json',
    '/tmp/foundations-liminf-limsup-material-source-components-review19-v1.json']
for p in new_reviews:
    assert p not in {x['file'] for x in out['independent_TMP_source_correspondence_reviews']}
    out['independent_TMP_source_correspondence_reviews'].append(review(p))

# Recheck every previously indexed passing proof, failed snapshot and immutable review/proposal.
main={x['file']:x['sha256'] for x in out['actual_new_unselected_proof_records']}
for row in out['actual_new_unselected_proof_records']:
    assert H(row['file'])==row['sha256'] and H(row['actual_standalone_evidence'])==row['actual_standalone_evidence_sha256']
    assert H(row['log'])==row['log_sha256']
    if 'preserved_source' in row:assert H(row['preserved_source'])==row['preserved_source_sha256']
for row in out['earlier_unselected_proof_recovery_annex']['previously_uncounted_sources_added_to_separate_recovered_scope']:
    assert H(row['source'])==row['source_sha256']
    for e in row['actual_source_matched_zero_evidence']:
        assert H(e['compiler_manifest'])==e['compiler_manifest_sha256'] and H(e['raw_log'])==e['raw_log_sha256']
for k in ['independent_TMP_source_correspondence_reviews','our_new_TMP_peer_reviews']:
    for row in out[k]:assert H(row['file'])==row['sha256']
for row in out['read_only_not_applied_proposals']:
    assert H(row['file'])==row['sha256'] and H(row['independent_review'])==row['independent_review_sha256']
for row in out['failed_execution_history']:
    assert H(row['file'])==row['sha256'] and H(row['source_snapshot'])==row['source_snapshot_sha256'] and H(row['log'])==row['log_sha256']

mp='reports/full-coverage/checkpoint-18-manifest.json';m=json.loads(P(mp).read_text());selected={}
for p,e in m['proof_files'].items():
    assert H(p)==e['sha256'];selected[p]=e['sha256']
    for ep,eh in e['evidence_sha256'].items():assert H(ep)==eh;selected[ep]=eh
assert not set(main)&set(m['proof_files'])
for p,h in m['frozen_inputs_sha256'].items():assert H(R/m['snapshot']/p)==h
out['preservation_check']=dict(manifest=mp,manifest_sha256=H(mp),selected_proof_files_checked=len(m['proof_files']),
    unique_current_selected_proof_and_evidence_paths_checked=len(selected),all_selected_paths_match=True,
    frozen_inputs_checked=len(m['frozen_inputs_sha256']),all_frozen_inputs_match=True,
    limits='Fresh read-only hashes; no aggregate/compiler rerun, axiom audit or checkpoint status change.')
assert len(m['proof_files'])==490 and len(selected)==565 and len(m['frozen_inputs_sha256'])==2431

out['prior_index']=prior;out['prior_index_sha256']=H(prior)
out['prior_index_original_timestamp_preserved']=old['prepared_at_utc']
out['prepared_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
out['counts']=dict(new_unselected_proof_files=len(main),
    new_actual_theorems=sum(len(x['declared_theorems']) for x in out['actual_new_unselected_proof_records']),
    independent_TMP_reviews=len(out['independent_TMP_source_correspondence_reviews']),
    our_TMP_peer_reviews=len(out['our_new_TMP_peer_reviews']),read_only_proposals=len(out['read_only_not_applied_proposals']))
assert out['counts']==dict(new_unselected_proof_files=57,new_actual_theorems=428,
    independent_TMP_reviews=55,our_TMP_peer_reviews=60,read_only_proposals=22)
recovered=out['earlier_unselected_proof_recovery_annex']['previously_uncounted_sources_added_to_separate_recovered_scope']
out['inclusive_recovered_owned_unselected_proof_counts']=dict(actual_zero_files=len(main)+len(recovered),
    actual_theorems=out['counts']['new_actual_theorems']+sum(len(x['declared_theorems']) for x in recovered),
    scope='Deduplicated union of57 main records and26 separately recovered earlier records; not live coverage or selected/frozen proof counts.')
assert out['inclusive_recovered_owned_unselected_proof_counts']['actual_zero_files']==83
assert out['inclusive_recovered_owned_unselected_proof_counts']['actual_theorems']==618
assert len(out['failed_execution_history'])==52
out['completed_prior_pending_review_updates'] += [
    dict(scope='987/988/990/996/1000/1002/1004/1007/1011/1023',
        review=new_reviews[1],sha256=H(new_reviews[1]),status='precise_source_review_received',
        limits='Whole987/996/1000/1002/1007/1011 approved.988/990 bounded epsilon scope,1004 failed-event attribution and1023 nonempty maximizer domain remain explicit pending source gaps. Original V1/time/body preserved.'),
    dict(scope='1025',review=new_reviews[2],sha256=H(new_reviews[2]),status='precise_component_review_received',
        limits='Seven true tail/finite-limit/liminf epsilon groups approved. Whole1025 remains pending actual four-power block-average example.')]
out['pending_new_source_correspondence_review_requests']=[]
proposal='/tmp/foundations-supremum-scope-proposal19.json'
assert H(proposal)=='19a6d719a6269249f67b097a2f8a196d9171da19a1737765986eb30b3e048b10'
out['pending_read_only_proposal_reviews']=[dict(file=proposal,sha256=H(proposal),reviewer='/root/applied_next',
    status='independent_peer_review_requested_not_yet_received',
    limits='Three exact source-line substitutions simulated only988/990/1004/1023 texts. No source write, serial, authorization or corrected-source whole promotion; excluded from approved proposal count.')]
failed_prep='/tmp/foundations-held-work-index-v17-first-preparation-failure.json'
out['preserved_failed_index_preparation']=dict(file=failed_prep,sha256=H(failed_prep),actual_exit_code=1,
    limits='Original helper used an incorrect manually predicted declaration total; no V17 index was written. Exact original failed helper snapshot was recovered and preserved separately.')
second_failure='/tmp/foundations-held-work-index-v17-second-preparation-failure.json'
second_helper='/tmp/foundations-prepare-held-work-index-v17-second-failed-helper.py'
out['preserved_second_failed_index_preparation']=dict(file=second_failure,sha256=H(second_failure),actual_exit_code=1,helper_snapshot=second_helper,helper_sha256=H(second_helper))
third_failure='/tmp/foundations-held-work-index-v17-third-preparation-failure.json'
third_helper='/tmp/foundations-prepare-held-work-index-v17-third-failed-helper.py'
out['preserved_third_failed_index_preparation']=dict(file=third_failure,sha256=H(third_failure),actual_exit_code=1,helper_snapshot=third_helper,helper_sha256=H(third_helper))
out['limits'] += [
    'V17 appends eight immutable actual-zero Foundation files/69 theorems: SupremumLesson18, SupremumExamples9, ExtendedRealValues10, MaximumExistence7, SafeOptExtendedBands6, ExtendedSupremumRules7, LiminfLimsupLesson7 and SupremumProofRoutes5. Seven standalone logs are empty; LiminfLimsupLesson retains one SeqFocus warning.',
    'Inclusive83 unique owned actual-zero unselected files/618 theorems includes the same earlier26-file recovery annex. These are passing-source artifact counts, not live coverage or checkpoint additions.',
    'All original52 own reviews remain exact; three separately saved independent literal/component reviews give55. Sixty peer reviews and22 independently approved readonly proposals remain exact. One new readonly supremum proposal has a pending independent review and is excluded from the approved count.',
    'Ten new genuine failed compiler histories are preserved, giving52 known failures. The original failed V17 index-preparation artifact remains immutable; no failed attempt relabeled passing.',
    'HOLD33 remains unreleased. No HTML/globalinventory/coverage/assets/builders/ledgers/offers were mutated. Fresh490/565/2431 preservation hashes and held metadata remain exact.'
]
q=pathlib.Path('/tmp/foundations-future19-held-work-index-v17.json');assert not q.exists()
q.write_text(json.dumps(out,indent=2)+'\n')
print(q,H(q),out['counts'],out['inclusive_recovered_owned_unselected_proof_counts'],len(out['failed_execution_history']))
