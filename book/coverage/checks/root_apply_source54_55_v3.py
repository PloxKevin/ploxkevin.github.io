"""Apply two approved source clarifications after both completed26 deliveries.

All exact-byte, semantic and fresh full29 parser guards precede every mutation.
Existing proof sources and installed owners remain unchanged; rebase is separate.
"""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,importlib.util,json,sys,tempfile
ROOT=Path(__file__).resolve().parents[3]
REPORTS=ROOT/'reports/full-coverage'
OUT=REPORTS/'source54-55-corrections-application-v1.json'
HISTORY=REPORTS/'source-history/approved-mpc-conformal-corrections54-55-20261011'
CONTRACT=Path('/tmp/root-source54-55-full29-parser-application-contract27-v2.json')
CONTRACT_SHA='0bf772e299fa974bb2ceddcfb3c5f9aaa9fc58412110c0dd954be5de405dfc9b'
PROPOSALS=[Path('/tmp/root-source54-continuity-and-domain-proposal-v3.json'),Path('/tmp/modules-conformal-source55-precision-proposal-v1.json')]
PROPOSAL_SHAS=['2a48b420bdea12ee86b659cc6d94181c22720249957ae6625c73d8b82a4316a1','7d75117fb9aef0240dea8326b9b76c480b424e4880e9c1b0fd2a29dc517b2ee5']
PEERS=[Path('/tmp/root-mpc-normbridge5-source54-proposal3-independent-modules-full-component-review27-v1.json'),Path('/tmp/modules-conformal-source55-independent-foundations-semantic-and-full29-parser-review-v1.json')]
PEER_SHAS=['0f5d29c601d50295c4c17879dc7af4d0cf141d554ee38683fdf5b689b5399d30','878ce997a50373af5c5b6a490e9e579ed713b2173a2b04dbb9399fc89232d728']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def safe(n):
    assert isinstance(n,str) and n and str(Path(n))==n and not Path(n).is_absolute() and '..' not in Path(n).parts
    assert not any(c in n for c in ('\0','\n','\r'))
    p=ROOT/n;assert p.resolve().is_relative_to(ROOT.resolve());return p
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def encoded(d):return (json.dumps(d,indent=2)+'\n').encode()
def write_new(p,data):
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('xb') as f:f.write(data)
def actual(stem):
    d=read(REPORTS/(stem+'.json'));values=[d[k] for k in ('actual_exit_code','exit_code') if k in d]
    assert values and all(type(v) is int and v==0 for v in values)
    assert sha(safe(d['log']))==d['log_sha256'];return d

def full_parser(candidates):
    parser=ROOT/'book/inventory_claims.py'
    assert sha(parser)=='b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
    with tempfile.TemporaryDirectory(prefix='root-source54-55-parser-') as td:
        isolated=Path(td);(isolated/'SafeLearning').mkdir()
        for page in (ROOT/'SafeLearning').glob('*.html'):
            n=page.relative_to(ROOT).as_posix();target=isolated/n
            if n in candidates:target.write_bytes(candidates[n])
            else:target.symlink_to(page)
        sys.path.insert(0,str(ROOT/'book'))
        spec=importlib.util.spec_from_file_location('source54_55_isolated_full_parser',parser)
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        module.ROOT=isolated;module.OUT=isolated/'book/coverage';module.inventory()
        data=(module.OUT/'inventory.json').read_bytes()
    assert sha(parser)=='b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
    return data,json.loads(data)

def inventory_diff(before,after,step):
    source=step['source'];digest=step['candidate']['sha256']
    assert after['counts']==before['counts']==step['counts']
    assert len(after['source_sha256'])==29
    assert after['source_sha256']=={**before['source_sha256'],source:digest}
    changed={}
    for field in ['exercises','material_source_units']:
        a={r['key']:r for r in before[field]};b={r['key']:r for r in after[field]}
        assert a.keys()==b.keys();changed[field]=[]
        for key in a:
            x=dict(a[key]);y=dict(b[key])
            if x['source']==source:
                assert y['source_sha256']==digest;x.pop('source_sha256');y.pop('source_sha256')
            if x!=y:
                assert {k:v for k,v in x.items() if k not in {'source_text','text_sha256'}}=={k:v for k,v in y.items() if k not in {'source_text','text_sha256'}}
                changed[field].append(key)
        assert changed[field]==step['exact_changed_text_keys'][field]
    return changed

def main():
    assert not OUT.exists() and not HISTORY.exists()
    assert sha(CONTRACT)==CONTRACT_SHA
    contract=read(CONTRACT);assert len(contract['steps'])==2
    inv_path=ROOT/'book/coverage/inventory.json';corr_path=ROOT/'book/coverage/material-corrections.json'
    assert sha(inv_path)==sha(ROOT/'book/coverage/inventory-after-correction53.json')==contract['before_inventory']['sha256']=='4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be'
    assert sha(corr_path)=='e63524a0d9fd13775e08b055d548fffc24036c1ae52825c196afe8583c95741d'
    corrections=read(corr_path);assert len(corrections['corrections'])==53
    assert [r['correction_id'] for r in corrections['corrections'][9:]]==list(range(10,54))
    for num in [54,55]:
        assert not (ROOT/f'book/coverage/inventory-before-correction{num}.json').exists()
        assert not (ROOT/f'book/coverage/inventory-after-correction{num}.json').exists()
    closer_path=ROOT/'book/coverage/checks/future27-core/closed-checkpoint26-delivery-originals-v2/closed-original-byte-aliases-v1.json'
    closer=read(closer_path)
    assert closer['status']=='completed_checkpoint26_actual_content_and_metadata_delivery_original_bytes_closed'
    assert closer['both_actual_pages_runs_and_all31_live_assets_passed'] is True
    assert closer['retained_failed_stager3_and_first_live_dns_attempt'] is True
    for row in closer['aliases']:
        assert sha(safe(row['original']['file']))==row['original']['sha256']
        assert sha(safe(row['immutable_original_byte_copy']['file']))==row['original']['sha256']
    live=read(REPORTS/'live-checkpoint-26-attempt3.json');pages=read(REPORTS/'pages-checkpoint-26-attempt3.json')
    assert live['status']=='passed_all31_asset_sha256' and live['commit']==live['remote_main']==pages['commit']==pages['expected_commit']==closer['metadata_commit']
    assert pages['status']=='passed';actual('live26-attempt3-execution-v1');actual('publication26-delivery-metadata-push-execution-v1')
    manifest=read(REPORTS/'checkpoint-26-manifest.json')
    assert manifest['status']=='formal_verification_passed_partial_coverage' and len(manifest['proof_files'])==1167
    assets={n:h for n,h in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')}
    owners={n:h for n,h in manifest['working_inputs_sha256'].items() if n in {
        'book/coverage/'+owner+'.json' for owner in ['core','foundations','applied','modules','applied-promotions']}}
    assert len(assets)==31 and len(owners)==5
    protected={n:r['sha256'] for n,r in manifest['proof_files'].items()};protected.update(assets);protected.update(owners)
    for n,h in protected.items():assert sha(safe(n))==h,n
    proposals=[];peers=[]
    evidence={str(CONTRACT):CONTRACT_SHA}
    for p,h,q,qh in zip(PROPOSALS,PROPOSAL_SHAS,PEERS,PEER_SHAS):
        assert sha(p)==h and sha(q)==qh
        proposals.append(read(p));peers.append(read(q));evidence[str(p)]=h;evidence[str(q)]=qh
    p54,p55=proposals;q54,q55=peers
    review54=q54['source54_proposal_review']
    assert q54['errors']==[] and review54['status']=='approved_full_source_semantic_correction_proposal_only'
    assert review54['missing_clauses']==[] and review54['all_full_original_assumptions_and_changed_paragraphs_read'] is True
    assert review54['proposal']=={'file':str(PROPOSALS[0]),'sha256':PROPOSAL_SHAS[0]}
    assert review54['entire_original_proposal3_body_and_time']==p54
    assert q55['errors']==[] and q55['proposal_approved'] is True
    assert q55['proposal']=={'file':str(PROPOSALS[1]),'sha256':PROPOSAL_SHAS[1]}
    assert q55['entire_original_proposal_body_and_time']==p55
    assert all(r['approved'] is True and r['missing_clauses']==[] for r in q55['exact_replacement_decisions'])
    original54=Path('/tmp/root-source54-continuity-and-domain-proposal-v1.json')
    assert sha(original54)=='312663377918b767f2010853fd51f41a07a389a7045fd198114c6411208d2da0'
    replacements54=copy.deepcopy(read(original54)['exact_five_replacements'])
    replacements54[2]['after']=replacements54[2]['after'].replace('the squared tracking error shrinking','the tracking certificate $V_\\delta$ shrinking')
    replacements54[4]['before']=', '+replacements54[4]['before'];replacements54[4]['after']='. '+replacements54[4]['after']
    replacement_sets=[replacements54,p55['exact_replacements']]
    candidates={};parsed=[];previous=read(inv_path)
    from validate import Document
    for step,proposal,replacements in zip(contract['steps'],proposals,replacement_sets):
        source=step['source'];original=safe(source).read_text();candidate=Path(step['candidate']['file'])
        assert proposal['candidate_only']==step['candidate'] and sha(candidate)==step['candidate']['sha256']
        assert proposal['current_source53']=={'file':source,'sha256':step['source_sha256_before']}
        assert sha(safe(source))==step['source_sha256_before']
        new=original
        for row in replacements:
            assert new.count(row['before'])==1 and row['after'] not in new
            new=new.replace(row['before'],row['after'],1)
        assert new.encode()==candidate.read_bytes() and new.count('\n')==original.count('\n')
        reverse=new
        for row in reversed(replacements):
            assert reverse.count(row['after'])==1;reverse=reverse.replace(row['after'],row['before'],1)
        assert reverse==original
        a=Document(original);b=Document(new)
        assert [(n.tag,n.attrs,n.line) for n in a.nodes]==[(n.tag,n.attrs,n.line) for n in b.nodes]
        candidates[source]=new.encode();data,after=full_parser(candidates)
        changed=inventory_diff(previous,after,step);parsed.append((step,replacements,data,after,changed));previous=after
    assert previous['source_sha256']==contract['final_page_sources_sha256']
    for table in [q54['evidence_sha256'],q55['closed_evidence_sha256']]:
        for n,h in table.items():
            assert n not in evidence or evidence[n]==h,n
            evidence[n]=h
    # Validate and preserve every semantic original before source/inventory changes.
    originals={}
    exact_external_aliases={}
    external_name='verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean'
    external_hash='e430f9176d3609cf18d6ae4abdd94a8bd6d30018734a7605b26de369968358ac'
    external_alias_name='book/coverage/checks/future27-core/source54-exact-mathlib-matrix-norm-original-v1.lean'
    for n,h in evidence.items():
        if n==external_name:
            assert h==external_hash and sha(ROOT/n)==h
            p=safe(external_alias_name);assert sha(p)==h
            exact_external_aliases[str(ROOT/n)]=str(p)
        else:
            p=Path(n) if Path(n).is_absolute() else safe(n)
        assert p.is_file() and not p.is_symlink()
        assert p.is_relative_to(ROOT) or p.parent==Path('/tmp')
        assert sha(p)==h,n;originals[str(p)]=h
    originals[str(Path('/tmp/root_prepare_source54_55_parser_contract27_v1.py'))]=sha(Path('/tmp/root_prepare_source54_55_parser_contract27_v1.py'))
    originals[str(Path('/tmp/root_prepare_source54_55_parser_contract27_v2.py'))]=sha(Path('/tmp/root_prepare_source54_55_parser_contract27_v2.py'))
    # No writes occurred above. All actual26/protected/semantic/full29 guards passed.
    root_copies={}
    for p in [inv_path,corr_path,*(safe(n) for n in owners),*(safe(step['source']) for step in contract['steps'])]:
        target=HISTORY/'source53-original-root'/p.relative_to(ROOT);write_new(target,p.read_bytes())
        assert sha(target)==sha(p);root_copies[p.relative_to(ROOT).as_posix()]=ref(target)
    aliases={}
    for n,h in originals.items():
        p=Path(n)
        target=HISTORY/('semantic-original-root' if p.is_relative_to(ROOT) else 'semantic-original-tmp')/(p.relative_to(ROOT) if p.is_relative_to(ROOT) else p.name)
        if target.suffix=='.txt':target=target.with_suffix('.txt.log')
        write_new(target,p.read_bytes());assert sha(target)==h;aliases[n]=ref(target)
    for original_name,canonical_name in exact_external_aliases.items():
        assert original_name not in aliases and canonical_name in aliases
        aliases[original_name]=aliases[canonical_name]
    history=HISTORY/'preserved-history.json'
    write_new(history,encoded({'status':'exact_source53_and_owner26_original_bytes_preserved_before_source54_55',
        'closed_at_utc':datetime.now(timezone.utc).isoformat(),'original_root_files':root_copies,
        'original_absolute_byte_aliases':aliases,'exact_original_external_source_aliases':exact_external_aliases,
        'entire_original_proposal_bodies_and_times':proposals,
        'entire_original_independent_semantic_review_bodies_and_times':peers,'delivered26_closure':ref(closer_path)}))
    applications=[]
    for step,replacements,data,after,changed in parsed:
        num=step['correction_id'];source=safe(step['source'])
        before=ROOT/f'book/coverage/inventory-before-correction{num}.json';following=ROOT/f'book/coverage/inventory-after-correction{num}.json'
        write_new(before,inv_path.read_bytes())
        if num==55:write_new(HISTORY/'material-corrections-after54-before55.json',corr_path.read_bytes())
        applied=datetime.now(timezone.utc).isoformat()
        source.write_bytes(candidates[step['source']]);inv_path.write_bytes(data);write_new(following,data)
        correction={'correction_id':num,'source':step['source'],'line':507 if num==54 else 840,
            'before_sha256':step['source_sha256_before'],'after_sha256':step['candidate']['sha256'],
            'replacements':replacements,'corrected_at_utc':applied,
            'status':'source_corrected_exact_independently_reviewed_scope_snippets_owner_identity_rebase_pending',
            'historical_source':root_copies[step['source']]['file'],'historical_source_sha256':step['source_sha256_before'],
            'preserved_history':ref(history),'independent_semantic_review':aliases[str(PEERS[num-54])],
            'scope':'MPC original continuity/domain/norm/certificate wording restored.' if num==54 else 'Conformal upper-bound joint no-ties and consistent calibration/test randomization precision. No new whole unit approval.'}
        corrections['corrections'].append(correction);corr_path.write_bytes(encoded(corrections))
        assert sha(source)==step['candidate']['sha256'] and sha(inv_path)==sha(following)
        applications.append({'correction_id':num,'applied_at_utc':applied,'source_after':ref(source),
            'inventory_before':ref(before),'inventory_after':ref(following),'exact_changed_text_keys':changed})
    changed_names={s['source'] for s in contract['steps']}
    for n,h in protected.items():
        if n not in changed_names:assert sha(safe(n))==h,n
    assert len(read(corr_path)['corrections'])==55
    record={'status':'passed_actual_source54_and_source55_corrections_full29_inventory_owner_identity_rebase_pending',
        'helper':ref(Path(__file__)),'applications':applications,'preserved_history':ref(history),
        'delivered26_metadata_commit':closer['metadata_commit'],'selected26_proof_sources_unchanged':1167,
        'other29_book_assets_unchanged':29,'five_installed26_owner_ledgers_unchanged':True,'coverage_complete':False,
        'scope':'Actual precisely reviewed source corrections/inventories only. Frozen26 and all original semantic review bodies/times remain exact; current owner identities require separate current55 review/integration. First planning reader incorrectly required a changed exercise at source54; that reader is preserved, and the final contract correctly lists none.'}
    write_new(OUT,encoded(record));print(json.dumps({'status':'passed','corrections':[54,55],'inventory_sha256':sha(inv_path),'coverage_complete':False}))
if __name__=='__main__':
    sys.path.insert(0,str(ROOT/'book'));main()
