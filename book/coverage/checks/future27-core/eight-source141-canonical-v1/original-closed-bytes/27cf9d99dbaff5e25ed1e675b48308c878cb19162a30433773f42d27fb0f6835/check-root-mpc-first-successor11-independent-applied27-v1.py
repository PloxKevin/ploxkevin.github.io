from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=Path('/tmp/CompleteCoreMPCFirstSuccessor27-draft-v1.lean');assert H(p)=='09fc59984a9e53f86e8ddfa82b2bee79f163aeffd5dc173b88eb6d8fc9c8000c';source=p.read_text()
bp=Path('/tmp/root-mpc-local-bootstrap27-independent-modules-full-component-review-v1.json');np=Path('/tmp/root-mpc-normbridge-two-new-components-independent-foundations-review27-v1.json')
assert H(bp)=='bee0502eede172581a4ebe30a07b8e3c3d21940cf56516f12ac991f1344c5c9e';assert H(np)=='4d14116582983c67038608af8b12fd1b142c85d39ff27fea103e03248331a9c7'
b=json.loads(bp.read_text());n=json.loads(np.read_text());assert b['errors']==n['errors']==[]
def declarations(s):
 out={};ns=None
 lines=s.splitlines(True);positions=[0]
 for line in lines:positions.append(positions[-1]+len(line))
 for i,line in enumerate(lines):
  m=re.match(r'^namespace (SafeLearning\.\w+)\s*$',line)
  if m:ns=m[1]
  m=re.match(r'^theorem (\w+)\b',line)
  if not m:continue
  stop=i+1
  while stop<len(lines)and not re.match(r'^(?:/--|theorem |def |private theorem |end SafeLearning\.|namespace |set_option |variable |attribute |open )',lines[stop]):stop+=1
  out[ns+'.'+m[1]]=''.join(lines[i:stop]).rstrip()
 return out
new=declarations(source);old3=declarations(b['entire_source']);old7=declarations(n['entire_source']);assert len(new)==11 and len(old3)==3 and len(old7)==7
for name,body in {**old3,**old7}.items():assert new[name]==body,('old body mismatch',name)
newname='SafeLearning.CompleteCoreMPCFirstSuccessor27.actual_first_disturbed_successor_is_in_X_and_in_the_local_tracking_sublevel';assert set(new)-set(old3)-set(old7)=={newname}
recordpath=Path('/tmp/root-mpc-first-successor27-trial1.json');record=json.loads(recordpath.read_text());assert type(record['actual_exit_code'])is int and record['actual_exit_code']==0 and type(record['actual_runner_exit_code'])is int and record['actual_runner_exit_code']==0
assert record['actual_command']==['lake','env','lean',str(p)]and record['actual_workdir']==str(R/'verification/lean')and record['protection_errors']==[]
assert H(record['source_snapshot'])==H(p)==record['source_sha256_before']==record['source_sha256_after']==record['source_snapshot_sha256']
assert H(record['raw_log'])==record['raw_log_sha256'];raw=Path(record['raw_log']).read_text();warnings=re.findall(r'^/tmp/CompleteCoreMPCFirstSuccessor27-draft-v1\.lean:\d+:\d+: warning:.*$',raw,re.M);assert len(warnings)==4
proposalpath=Path('/tmp/root-source54-continuity-and-domain-proposal-v3.json');assert H(proposalpath)=='2a48b420bdea12ee86b659cc6d94181c22720249957ae6625c73d8b82a4316a1';proposal=json.loads(proposalpath.read_text());candidate=Path(proposal['candidate_only']['file']);assert H(candidate)==proposal['candidate_only']['sha256'];html=candidate.read_text();setting='\n'.join(html.splitlines()[502:550]);assert 'continuous in its first state argument' in setting and 'Choose a positive Lipschitz bound' in setting and 'The first disturbed successor must first be kept in $X$'in setting
primary=R/proposal['primary_original']['file'];assert H(primary)==proposal['primary_original']['sha256'];primarybody=primary.read_text();primarylines=primarybody.splitlines();primarycontext='\n'.join(primarylines[77:234])
assert 'continuous in the first argument' in primarycontext and 'Assumption 2' in primarycontext and 'Assumption 3' in primarycontext
# Closed original evidence remains historical: preserved outcomes/times are not relabelled.
closed={str(p):H(p),str(bp):H(bp),str(np):H(np),str(recordpath):H(recordpath),record['raw_log']:H(record['raw_log']),record['source_snapshot']:H(record['source_snapshot']),str(proposalpath):H(proposalpath),str(candidate):H(candidate),str(primary):H(primary),record['original_actual_runner']['file']:record['original_actual_runner']['sha256']}
for owner,digest in record['installed26_owner_sha256'].items():assert H(R/owner)==digest
selectionpath=R/'reports/full-coverage/checkpoint-26-selection.json';assert H(selectionpath)==record['actual_installed26_selection']['sha256'];selection=json.loads(selectionpath.read_text());assert len(selection['proof_files'])==1167
for name,row in selection['proof_files'].items():assert H(R/name)==row['sha256']
for key in ['evidence_sha256','closed_evidence_sha256']:
 for old in [b,n]:
  for name,digest in old.get(key,{}).items():
   real=Path(name)if Path(name).is_absolute()else R/name;assert H(real)==digest;closed[name]=digest
for name,digest in closed.items():assert H(Path(name)if Path(name).is_absolute()else R/name)==digest
# The declaration proves domain membership first, then IVT bootstrap; no locality conclusion is a supplied premise.
newbody=new[newname];assert newbody.index('have hactual')<newbody.index('have hlocalvalue')
assert '(hlocal :'in newbody and 'V y z v ≤ delta →'in newbody
component={'component_id':'actual_first_disturbed_successor_domain_then_local_sublevel','status':'approved_precise_component','lean_declarations':[newname],'source_unit_keys':['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739','lyapunov-mpc.html::node-1387'],'hypotheses':['Actual finite real matrix polytopic state domain X={Hx<=1}; state is Euclidean, input perturbation norm is coordinate infinity.','lambda>0,eta>=0,delta>0,cU>0,margin>=0 and genuine Assumption3 eta<=lambda inverse*sqrt(delta/cU).','Actual original Assumption2 on X and allowed u,u+d in U; current x in X; norm∞(d)<=eta.','The actual nominal successor satisfies every row<=1-margin and ||H||∞*(lambda*eta)<=margin. Deriving this margin from the printed epsilon/tube formula is separate.','Fixed shifted vnext belongs to U; V is continuous in its first argument on X, vanishes at nominal equality, and only conditionally obeys the upper quadratic bound inside V<=delta for all actual X/X/U arguments.'],'per_component_reason':'The actual Assumption2 gives Euclidean successor error<=lambda*eta. The genuine infinity-row-sum/Euclidean-state matrix bridge combines that radius with the supplied tightened nominal margin to prove the disturbed successor belongs to X first; margin>=0 also places the nominal successor in X. Convexity of the exact row intersection gives the whole joining segment inside X. Assumption3 yields cU*(lambda*eta)^2<=delta, and the actual error-radius square is smaller. The continuous first-crossing bootstrap uses only the conditional local quadratic estimate and V(z,z,v)=0 to derive the endpoint estimate, without assuming endpoint locality. This then bounds the actual V value by cU*(lambda*eta)^2<=delta.','missing_clauses':[]}
remaining=['The printed epsilon formula must still be connected to an actual tightened nominal successor/input margin for every predicted step. This component retains its concrete margin hypotheses.','Genuine predicted incremental feedback recursion and all shifted state/input domain conditions, terminal reach/shift and optimizer existence remain separate.','No general Assumptions1–4=>robustOneStepCertificate, all-time robust MPC/finite-entry proof or whole Exercise18/material1387 decision follows.','Source54 candidate is reviewed here for this exact component correspondence only; actual source application/parser/current55 identity and canonical/named proof selection are separate.']
out=Path('/tmp/root-mpc-first-successor11-independent-applied-full-component-review27-v1.json');assert not out.exists();out.write_text(json.dumps({'status':'passed_independent_full_new_first_successor_component_and_exact_old_ten_body_review','errors':[],'reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'proof_source':{'file':str(p),'sha256':H(p)},'entire_source':source,'all11_complete_bodies_read':True,'all_public_theorem_names':list(new),'public_theorem_count':11,'new_component':component,'whole_exercise_approved':False,'whole_material_unit_approved':False,'original_bootstrap3_peer':{'file':str(bp),'sha256':H(bp)},'entire_original_bootstrap3_peer_body_and_time':b,'original_norm7_peer':{'file':str(np),'sha256':H(np)},'entire_original_norm7_peer_body_and_time':n,'all_original_ten_body_bytes_preserved':True,'source54_candidate':proposal['candidate_only'],'entire_original_source54_proposal_body_and_time':proposal,'complete_candidate_assumption_and_validation_context_read':setting,'complete_primary_domain_and_assumption_context_read':primarycontext,'actual_standalone':{'file':str(recordpath),'sha256':H(recordpath)},'entire_original_actual_standalone_record':record,'actual_warning_lines':warnings,'remaining_gaps':remaining,'protected_original1167_sources_and_five_owners_rehashed_exact':True,'closed_evidence_sha256':closed,'scope':'TMP-only independent full new proof/component and exact old-ten-body/peer preservation. No new compiler, canonical/named build, source/proof/owner/current26/PUB/Git write or whole coverage decision. Original actual trial0 and four genuine warning lines/times retained.'},indent=2)+'\n');print(json.dumps({'peer':str(out),'sha256':H(out),'new_components':1,'old_bodies_exact':10,'public_total':11,'closed_originals':len(closed)}))
