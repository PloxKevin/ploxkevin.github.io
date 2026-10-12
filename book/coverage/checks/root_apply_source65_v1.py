"""Apply the two independently reviewed scalar-SDP qualifiers, preserving64.

No coverage/owner decision is made. A fresh complete parser and every byte guard
finish before writes; all original receipts retain their actual bodies/times.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json
ROOT=Path(__file__).resolve().parents[3]
SELF='book/coverage/checks/root_apply_source65_v1.py'
PROPOSAL={'file':'book/coverage/checks/modules-future29/scalar-lipsdp42-and-source65-v1/original-closed-bytes/1816acd6bfc2c44cb7fd5ce76ce01c380bca0cb996ea9947ef1187a916cd0d1e/modules-scalar-sdp-source65-proposal29-current64-v3.json','sha256':'1816acd6bfc2c44cb7fd5ce76ce01c380bca0cb996ea9947ef1187a916cd0d1e'}
CONTEXT=Path('/tmp/root_tmp_lean_current64_owner28_context_v1.json')
CONTEXT_SHA='442590b45444a97af4b12a37b9ee3f6166b6118a85516e339c6d55bb0c33c6e0'
HISTORY='reports/full-coverage/source-history/approved-correction65-20261011'
REPORT='reports/full-coverage/source65-correction-application-v1.json'
spec=importlib.util.spec_from_file_location('source65_full29_parser',ROOT/'book/coverage/checks/root_apply_source54_55_v3.py');b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
def locate(n):
    p=Path(n) if Path(n).is_absolute() else b.safe(n)
    assert p.is_file() and not p.is_symlink() and (p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to('/tmp'))
    return p
def checked(r):
    p=locate(r['file']);assert b.sha(p)==r['sha256'];return p
def ref(n):return {'file':n,'sha256':b.sha(locate(n))}
def guard(context):
    assert b.sha(CONTEXT)==CONTEXT_SHA
    for n,h in {**context['pins_sha256'],**context['held_current_source_sha256']}.items():checked({'file':n,'sha256':h})
    assert b.sha(ROOT/'book/coverage/checks/root_apply_source54_55_v3.py')=='6b4c52ce05d8ed940a22982107b2ba708dc0f6f28e1a60ab4396b78c68286be0'
    assert not (ROOT/HISTORY).exists() and not (ROOT/REPORT).exists()
    assert not (ROOT/'book/coverage/inventory-before-correction65.json').exists() and not (ROOT/'book/coverage/inventory-after-correction65.json').exists()
    assert len(b.read(ROOT/'book/coverage/material-corrections.json')['corrections'])==64

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--peer',required=True);ap.add_argument('--peer-sha256',required=True);ap.add_argument('--apply',action='store_true');args=ap.parse_args()
    context=b.read(CONTEXT);guard(context)
    peerref={'file':args.peer,'sha256':args.peer_sha256};peer=b.read(checked(peerref))
    assert peer['status'].startswith('passed_independent_') and peer['errors']==[]
    assert peer['proposal']['sha256']==PROPOSAL['sha256']
    assert len(peer['narrow_wording_decisions'])==2 and all(r['approved'] is True for r in peer['narrow_wording_decisions'])
    assert type(peer['first_actual_reader_exit_code']) is int and peer['first_actual_reader_exit_code']==0
    receipt=checked(peer['actual_finalizer']);native=b.read(receipt)
    assert type(native['actual_exit_code']) is int and native['actual_exit_code']==0
    for n,h in peer['required_evidence_artifacts_sha256'].items():checked({'file':n,'sha256':h})
    proposal=b.read(checked(PROPOSAL));source=proposal['source']['file'];assert source=='SafeLearning/lipsdp.html'
    checked(proposal['source']);checked(proposal['proposed_source'])
    original=locate(source).read_text();new=original
    for r in proposal['exact_replacements']:
        assert new.count(r['before'])==1 and r['after'] not in new;new=new.replace(r['before'],r['after'],1)
    assert len(proposal['exact_replacements'])==2 and new.encode()==checked(proposal['proposed_source']).read_bytes()
    reverse=new
    for r in reversed(proposal['exact_replacements']):
        assert reverse.count(r['after'])==1;reverse=reverse.replace(r['after'],r['before'],1)
    assert reverse==original and new.count('\n')==original.count('\n')
    import sys;sys.path.insert(0,str(ROOT/'book'));from validate import Document
    assert [(n.tag,n.attrs,n.line) for n in Document(original).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
    step={'source':source,'candidate':proposal['proposed_source'],'exact_changed_text_keys':proposal['fresh_changed_literal_keys'],'counts':proposal['counts']}
    data,following=b.full_parser({source:new.encode()});changed=b.inventory_diff(b.read(ROOT/'book/coverage/inventory.json'),following,step)
    assert changed=={'exercises':['lipsdp.html::exercise-19'],'material_source_units':['lipsdp.html::node-1328','lipsdp.html::node-1329']}
    protected={**context['pins_sha256'],**context['held_current_source_sha256']}
    guard(context)
    if not args.apply:print(json.dumps({'status':'ready_exact_source65_full29_no_live_writes','coverage_complete':False}));return
    original_names=['book/coverage/inventory.json','book/coverage/material-corrections.json',source]
    aliases={};copies={}
    for n in original_names:
        target=HISTORY+'/source64-original/'+n;copies[target]=ref(n);aliases[n]={'file':target,'sha256':b.sha(locate(n))}
    for row in [PROPOSAL,peerref,ref(str(receipt)),ref(SELF),ref(str(CONTEXT))]:
        pp=checked(row);target=HISTORY+'/semantic-original-by-sha256/'+row['sha256']+'/'+pp.name
        copies[target]=row;aliases[row['file']]={'file':target,'sha256':row['sha256']}
    for n,r in copies.items():assert not (ROOT/n).exists();checked(r)
    for n,r in copies.items():b.write_new(ROOT/n,checked(r).read_bytes());checked({'file':n,'sha256':r['sha256']})
    history=HISTORY+'/preserved-history-v1.json'
    b.write_new(ROOT/history,b.encoded({'status':'exact_source64_and_original_source65_review_bytes_preserved_before_application','preserved_at_utc':datetime.now(timezone.utc).isoformat(),'original_byte_aliases':aliases,'old_five_owner28_bytes_preserved_at':'reports/full-coverage/source-history/approved-corrections61-64-20261011/source60-owner28-original/book/coverage','coverage_complete':False}))
    before='book/coverage/inventory-before-correction65.json';after='book/coverage/inventory-after-correction65.json'
    corrections=b.read(ROOT/'book/coverage/material-corrections.json');b.write_new(ROOT/before,locate('book/coverage/inventory.json').read_bytes())
    applied=datetime.now(timezone.utc).isoformat();locate(source).write_bytes(new.encode());locate('book/coverage/inventory.json').write_bytes(data);b.write_new(ROOT/after,data)
    corrections['corrections'].append({'correction_id':65,'source':source,'before_sha256':proposal['source']['sha256'],'after_sha256':proposal['proposed_source']['sha256'],'replacements':proposal['exact_replacements'],'corrected_at_utc':applied,'status':'source_corrected_exact_independently_reviewed_scope_snippets_owner_identity_rebase_pending','source_proposal':aliases[PROPOSAL['file']],'independent_semantic_review':aliases[peerref['file']],'preserved_history':ref(history),'inventory_before':ref(before),'inventory_after':ref(after),'scope':'Only the exact positive-supremum qualification and eigenvalue precision. Full mathematics/owner promotion is separately reviewed.'})
    locate('book/coverage/material-corrections.json').write_bytes(b.encoded(corrections))
    changed_names={source,'book/coverage/inventory.json','book/coverage/material-corrections.json'}
    for n,h in protected.items():
        if n not in changed_names:checked({'file':n,'sha256':h})
    assert b.sha(locate(source))==proposal['proposed_source']['sha256'] and b.sha(ROOT/after)==b.sha(ROOT/'book/coverage/inventory.json')
    assert len(b.read(ROOT/'book/coverage/material-corrections.json')['corrections'])==65
    record={'status':'passed_actual_source65_correction_full29_inventory_owner_identity_rebase_pending','helper':ref(SELF),'applied_at_utc':applied,'source_after':ref(source),'inventory_before':ref(before),'inventory_after':ref(after),'preserved_history':ref(history),'independent_peer':peerref,'exact_changed_text_keys':changed,'selected28_proof_sources_unchanged':1186,'other64_book_assets_unchanged':30,'five_owner28_ledgers_unchanged':True,'coverage_complete':False}
    b.write_new(ROOT/REPORT,b.encoded(record));print(json.dumps({'status':record['status'],'inventory':ref('book/coverage/inventory.json'),'coverage_complete':False}))

if __name__=='__main__':main()
