from pathlib import Path
import re
R=Path('/home/oxrexkevin/SafetyBased')
s=(R/'book/coverage/checks/future24-core/modules-checkpoint24-production-output-peer-v2.py').read_text()
s=s.replace('24','__NEXT__').replace('23','24').replace('__NEXT__','25')
s=s.replace('9831539a3b2be8c9d7878fd004354511aa332b203e40506233d0a000dca805fb','9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314')
s=s.replace('e21eac7bfafd8002d75966240e5c3ea940ebec3dba4066fb1e9a767627d7fb06','5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0')
# Global numeric replacement above also touched literal SHA substrings; restore every fixed digest from its literal original.
old=(R/'book/coverage/checks/future24-core/modules-checkpoint24-production-output-peer-v2.py').read_text()
for h in set(re.findall(r'[0-9a-f]{64}',old)):
 transformed=h.replace('24','__NEXT__').replace('23','24').replace('__NEXT__','25')
 s=s.replace(transformed,h)
s=s.replace('9831539a3b2be8c9d7878fd004354511aa332b203e40506233d0a000dca805fb','9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314').replace('e21eac7bfafd8002d75966240e5c3ea940ebec3dba4066fb1e9a767627d7fb06','5e0a58f71b685edbd3bbf7c965a2fda3ffd18f8edfde75c5bf810c7bb63d18e0')
s=re.sub(r'\b1144\b','1156',s);s=re.sub(r'\b1131\b','1144',s);s=re.sub(r'\b36910\b','40485',s);s=re.sub(r'\b9279\b','9369',s);s=re.sub(r'\b13\b','12',s)
s=s.replace('prepare_checkpoint25_selection_v4.py','prepare_checkpoint25_selection_v3.py')
s=s.replace('c2c91bf3ec80c845525bd205abfe8a1cd1da03a8b27e01590a1434da5fedb4ae','a788a6a0f07da24dff706a02189bf93f9a858913f75bfb5f315982065ae1ea88')
s=s.replace('19bac8959fcf9e737ca8bef9b78026476f0369b64850f0f473048448e099d781','f1f8f6edc97ba10781c850b0953d7a2b9eabe607e791b88bb36b03742904e4a7')
s=s.replace("assert changed_assets=={'SafeLearning/nn-in-the-loop.html'}","assert changed_assets==set()")
s=s.replace('57df986e038a2867b8a4c0b3247abbfaa8845bcaa9db52a69074dea8776250ef','61e5f01dc3bc671d93e543caef716bc343933d0ba9f60a680d26b96e9e6b042d')
s=s.replace("plan['prior_checkpoint24_alias_repair_provenance']","plan['prior_checkpoint24_selection_provenance']")
s=s.replace("'names25_output'","'names25_output'")
s=s.replace("'baseline24_selection':ref(BASELINE)","'baseline24_selection':ref(BASELINE)")
# Preserve native23/24 pruning distinction; singleton future code is checked separately.
anchor="aliases=authorization['aliases'];assert set(aliases)==set(replacements)-{'book/coverage/applied-promotions.json'}"
extra='''updates=native['authorized_current_future_code_updates']
assert set(updates)=={'book/coverage/checks/run_root_barrier_control25_canonical_pair_v1.py'}
update_name=next(iter(updates));update=updates[update_name]
assert update['old_working_sha256']=='f98e1a5ed31c6641ee15b3ecb00af0f0268bb0518d1cf5f125447320b1554ca6'
assert update['current_sha256']=='53d47e49148a10f3dca53fff80514219e814764f557ae8f809c0d3dd28221fc6'==sha(update_name)
assert update['original_frozen_input']=={'file':manifest['snapshot']+'/'+update_name,'sha256':update['old_working_sha256']}
assert sha(update['original_frozen_input']['file'])==manifest['working_inputs_sha256'][update_name]==manifest['frozen_inputs_sha256'][update_name]==update['old_working_sha256']
future_authorization=checked(native['current_future_code_update_authorization'])
assert future_authorization['authorized_current_future_code_updates']==updates
assert len(native['authorized_current_future_code_update_reference_sha256'])==17
exact(native['authorized_current_future_code_update_reference_sha256'])
first_actual=checked(update['actual_first_execution']);zero(first_actual)
assert first_actual['helper_sha256_before']==first_actual['helper_sha256_after']
assert update['current_sha256'] in first_actual['helper_sha256_after'].values()
assert sha(update['raw_log']['file'])==update['raw_log']['sha256']==first_actual['log_sha256']
independent_delta=checked(update['independent_delta_peer']);assert 'passed' in independent_delta['status'] and independent_delta.get('errors',[])==[]
'''
s=s.replace(anchor,extra+anchor)
s=s.replace("'all_claim_declarations_selected':True,","'all_claim_declarations_selected':True,'authorized_single_future_code_update_exact':True,'authorized_future_code_closed_reference_count':17,")
s=s.replace("checked_at_utc':datetime.now(timezone.utc).isoformat()","checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/modules_resume'")
p=Path('/tmp/modules-checkpoint25-production-output-peer-v1.py');assert not p.exists();p.write_text(s)
