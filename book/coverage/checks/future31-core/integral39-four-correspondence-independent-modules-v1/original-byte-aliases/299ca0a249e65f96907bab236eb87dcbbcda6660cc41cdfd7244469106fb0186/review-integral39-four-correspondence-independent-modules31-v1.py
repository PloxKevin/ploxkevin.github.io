from pathlib import Path
import hashlib,json,re,sys
R=Path('/home/oxrexkevin/SafetyBased');S=Path('/tmp/applied-finish31-integral35-correspondence-v2.lean');P=R/'book/coverage/checks/future31-applied/integral35-whole-independent-v1/integral35-entire-current-prospective-independent-applied31-peer-v1.json';C=Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json');OUT=Path('/tmp/integral39-four-correspondence-independent-modules31-findings-v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(x):
 p=Path(x['file']);return p if p.is_absolute()else R/p
refs=[]
def ref(p):
 p=Path(p);x={'file':str(p.relative_to(R))if p.is_relative_to(R)else str(p),'sha256':sha(p),'bytes':p.stat().st_size};refs.append(x);return x
assert sha(S)=='1a388e0109e6e8ff8bd9ce8c102420a7202f064eb7e46a76ff2cd4bcfefc10aa'
assert sha(P)=='e0d997d45d8d5387cba74e87adc8cc37ac8afec394dfdb0370f12b7f9a3e48c0'
assert sha(C)=='f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
c=json.loads(C.read_bytes());guards={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']}
def guard():
 assert sha(C)=='f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
 for n,h in guards.items():
  p=R/n;assert p.is_file()and not p.is_symlink()and p.resolve().is_relative_to(R)and sha(p)==h,n
 assert sha(S)=='1a388e0109e6e8ff8bd9ce8c102420a7202f064eb7e46a76ff2cd4bcfefc10aa'
 assert sha(P)=='e0d997d45d8d5387cba74e87adc8cc37ac8afec394dfdb0370f12b7f9a3e48c0'
guard();q=json.loads(P.read_bytes());assert q['errors']==[]and q['status'].startswith('passed_')
for n,h in q['required_evidence_artifacts_sha256'].items():assert sha(R/n)==h
base=path(q['entire_source']);assert sha(base)=='384484a7fb9d48fcb00c76a52b004ae3bbf3697b4acc71b14c9f7c0f0f17fc9a'
s=S.read_bytes();assert s.startswith(base.read_bytes());increment=s[len(base.read_bytes()):].decode();text=s.decode()
sys.dont_write_bytecode=True;sys.path.insert(0,str(R/'book/coverage'));import lean_names
names=[d['name']for d in lean_names.declarations(text)if d['kind']in ['theorem','lemma']and d['visibility']!='private']
assert len(names)==39
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',lean_names.without_comments(text))
local=['literal_scalar_derivative_and_full_interval','physical_all_reference_global_exponential_estimate','exact_true_plant_feedforward_requirement','pure_gain_mismatch_zero_reference_exception']
blocks=[]
for j,name in enumerate(local):
 start=increment.index('theorem '+name);end=increment.index('theorem '+local[j+1])if j+1<len(local)else increment.index('end SafeLearning.AppliedFinish31Integral35Correspondence')
 block=increment[start:end];blocks.append({'name':'SafeLearning.AppliedFinish31Integral35Correspondence.'+name,'full_proof_body_read':True,'source_block_sha256':hashlib.sha256(block.encode()).hexdigest(),'source_block':block})
hist=[]
for j in [1,2]:
 p=Path(f'/tmp/applied-finish31-integral35-correspondence-native-v{j}.json');n=json.loads(p.read_bytes());raw=Path(n['raw_log']).read_bytes();source=Path(n['source']);snap=Path(n['source_snapshot'])
 assert n['actual_exit_code']==n['actual_runner_exit_code']==[1,0][j-1]and n['protection_errors']==[]and n['source_unchanged']is True
 assert sha(source)==n['source_sha256_before']==n['source_sha256_after']==sha(snap)==n['source_snapshot_sha256']
 assert sha(n['raw_log'])==n['raw_log_sha256']and n['actual_command']==['lake','env','lean',str(source)]and n['actual_workdir']==str(R/'verification/lean')
 assert len(re.findall(rb'^.*?:\d+:\d+: warning:',raw,re.M))==11
 for k in ['original_actual_runner','actual_source79_final_css_owner30_context']:assert sha(path(n[k]))==n[k]['sha256'];ref(path(n[k]))
 hist.append({'native':ref(p),'source':ref(source),'snapshot':ref(snap),'raw_log':ref(n['raw_log']),'actual_exit_code':n['actual_exit_code'],'emitted_warning_headers':11,'original_body_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
raw=Path('/tmp/applied-finish31-integral35-correspondence-native-v2.log').read_text()
for name in local:
 pattern=re.escape("'SafeLearning.AppliedFinish31Integral35Correspondence."+name+"' depends on axioms:")+r'\s*\[([^]]+)\]'
 m=re.search(pattern,raw);assert m and{z.strip()for z in m[1].split(',')}=={'propext','Classical.choice','Quot.sound'}
inv=json.loads((R/'book/coverage/inventory-after-correction81.json').read_bytes());units={x['key']:x for x in inv['material_source_units']};exs={x['key']:x for x in inv['exercises']}
actual={}
for k,prospective in q['entire_prospective_exercise_and_changed_literal'].items():
 row=(exs if '::exercise-'in k else units)[k];assert row['source_text']==prospective['entire_proposed']['source_text'];actual[k]=row
for k in ['nn-in-the-loop.html::node-1240','nn-in-the-loop.html::node-1244','nn-in-the-loop.html::node-1249']:
 oldrow=next(x for x in q['full_current_literals']if x['key']==k);assert units[k]['source_text']==oldrow['source_text'];actual[k]=units[k]
assessments=[
'Actual derivative is built from tanh derivative via composition with x-r, constant network multiplication and the physical scalar sum. Since b is in [1,6/5] and tanh derivative is in (0,1], the removed derivative contribution is in [0,9/25], yielding [7/50,1/2]=[0.14,0.5] for every x,d,r. No desired derivative interval is a hypothesis.',
'Exact physical-to-centered-error trajectory identity discharges the association to all real references/disturbances and all initial physical states. For the two specified gains, the already-proved nonlinear quadratic estimate gives the displayed sqrt(10)*(sqrt(39/40))^n bound on the actual physical output/integrator error.',
'True fixed output r is equivalent to its true steady-state feedforward (r/2-d)/b when b is nonzero. This is the actual scalar plant with a=1/2 and its held-fixed nominal network. It permits a controller accurately matched to one true plant; it does not claim impossibility for an individual known model.',
'For gain6/5, disturbance0 and the held nominal network, zero output error at equilibrium is equivalent to r=0. The exception is explicit, so wrong-value claims at r=1 are not strengthened to every reference.'
]
for x,a in zip(blocks,assessments):x['mathematical_assessment']=a;x['approved']=True;x['remaining_gaps']=[]
guard()
f={'status':'passed_independent_integral39_exact35_prefix_four_added_correspondence_full_proof_review','errors':[],'reviewer':'/root/modules_finish28','source':ref(S),'original35_entire_source':ref(base),'original35_full_independent_whole_peer':ref(P),'exact35_original_byte_prefix_retained':True,'all39_public_names':names,'increment4_individual_decisions':blocks,'all4_full_proof_bodies_and_used_base_bodies_read':True,'original_full35_semantic_decisions_body_times_unchanged':True,'actual_source81_literal_equalities_to_approved_prospective_and_unchanged_current':actual,'source81_application':ref(R/'reports/full-coverage/source80-81-corrections-application-v3.json'),'source81_context':ref(C),'actual_supplemental_native_histories':hist,'all4_printed_axiom_lists_standard_three_only':True,'source81_current_inputs_guarded_sha256':guards,'actual_input_refs':refs,'protected_selected30_proof_sources':1242,'current_source81_final_css_assets':31,'unchanged_historical_source79_raw_owner30_files':5,'compiler_or_owner_source_canonical_publication_mutation':False,'aggregate_source81_verification_claimed':False,'coverage_complete':False,'whole_scope':'This independent review approves the four author-added correspondence bodies only, transfers the unchanged35 full semantic decisions by exact prefix/literal equality and binds actualSource81 text. It does not silently rewrite the original35 historical current=false/prospective=true verdicts, install proofs or rebase raw ownership.'}
with OUT.open('x')as p:json.dump(f,p,indent=2);p.write('\n')
print(json.dumps({'findings':ref(OUT),'increment_all4_approved':True,'errors':[]}))
