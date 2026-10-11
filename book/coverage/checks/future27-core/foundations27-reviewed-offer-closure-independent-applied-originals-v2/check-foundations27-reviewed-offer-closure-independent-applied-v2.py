from pathlib import Path
import copy, hashlib, importlib.util, json
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER=ROOT/'book/coverage/checks/root_close_foundations27_reviewed_offer_v2.py'
OUT=Path('/tmp/foundations27-reviewed-offer-closure-independent-applied-check-result-v2.json')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(HELPER)=='cf02346ec05bca13557cb5fd97dafb15933d23c8ed10cbec13403b8a82f1fa64'
spec=importlib.util.spec_from_file_location('independent_readonly_foundations27_closure2',HELPER)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
assert not module.DEST.exists() and not module.ARCHIVE.exists()
old,new,copies=module.prepare()
assert not module.DEST.exists() and not module.ARCHIVE.exists()
assert new['proof_files']==old['proof_files'] and new['candidate']==old['candidate']
assert len(old['proof_files'])==3 and new['new_theorem_or_lemma_count']==43
assert new['original_final_independent_peer_body_and_time']==json.loads(module.PEER.read_bytes())
inverse=copy.deepcopy(new);finalization=inverse.pop('offer_finalization')
inverse['additional_frozen_inputs']=finalization['original_additional_frozen_inputs']
for k,row in finalization['original_fields'].items():
    if row['present']:inverse[k]=row['value']
    else:inverse.pop(k)
assert inverse==old
for target,(source,h) in copies.items():
    assert target.is_relative_to(module.ARCHIVE) and not target.exists() and sha(source)==h
assert len(old['proof_files'])==3
peer=json.loads(module.PEER.read_bytes())
assert len(peer['genuine_canonical_compiler_commands'])==6
fixtures=[]
def reject(name,action):
    try:action()
    except (AssertionError,KeyError,TypeError,ValueError,FileNotFoundError):fixtures.append({'fixture':name,'result':'rejected'});return
    raise AssertionError('unexpected acceptance '+name)
module.zero({'actual_exit_code':0,'exit_code':0,'actual_runner_exit_code':0});fixtures.append({'fixture':'all-present exact integer zeros','result':'accepted'})
for name,body in [('boolean-false',{'actual_exit_code':False}),('float-zero',{'exit_code':0.0}),('missing-code',{}),('conflicting-runner-code',{'actual_exit_code':0,'actual_runner_exit_code':1}),('null-code',{'actual_exit_code':None})]:reject(name,lambda b=body:module.zero(b))
valid={'file':str(module.OFFER),'sha256':module.OFFER_SHA}
module.checked(valid);fixtures.append({'fixture':'exact original offer typed reference','result':'accepted'})
reject('wrong original offer digest',lambda:module.checked({**valid,'sha256':'0'*64}))
reject('extra typed reference key',lambda:module.checked({**valid,'extra':True}))
reject('traversal path',lambda:module.locate('../outside.json'))
reject('outside absolute path',lambda:module.locate('/etc/passwd'))
assert sha(module.OFFER)==module.OFFER_SHA and sha(ROOT/module.OLD)==module.OLD_SHA and sha(ROOT/'book/coverage/inventory.json')==module.INV_SHA
result={'status':'passed_independent_read_only_foundations27_offer_closure_helper2_checker','errors':[],'helper':{'file':str(HELPER.relative_to(ROOT)),'sha256':sha(HELPER)},'original_offer':{'file':str(module.OFFER.relative_to(ROOT)),'sha256':sha(module.OFFER)},'candidate':new['candidate'],'source_count':3,'public_theorem_count':43,'real_canonical_command_count':6,'planned_original_copy_count':len(copies),'fixture_count':len(fixtures),'fixtures':fixtures,'exact_reverse_to_entire_original_offer':True,'full_original_peer_body_hypotheses_reasons_and_time_preserved':True,'all_candidate_proof_and_math_fields_unchanged':True,'readonly_prepare_called':True,'execute_called':False,'no_dest_or_archive_created':True,'original_author_first_preflight_failure_preserved':finalization['original_author_preflight_sha256'],'scope':'Independent full source/delta and native prepare read-only check only; actual offer writes still require Root. No compiler, installed-owner, selection, aggregate, or publication action.'}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'fixtures':len(fixtures),'planned_copies':len(copies),'result':str(OUT),'sha256':sha(OUT)}))
