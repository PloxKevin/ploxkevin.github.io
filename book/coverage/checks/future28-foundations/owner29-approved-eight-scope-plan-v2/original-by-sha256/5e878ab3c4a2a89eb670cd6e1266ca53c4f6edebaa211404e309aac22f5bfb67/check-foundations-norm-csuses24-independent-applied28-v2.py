from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,time
R=Path('/home/oxrexkevin/SafetyBased');request=Path('/tmp/foundations-norm-csuses24-four-full-literals-review28-v1.json');context=Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
c=json.loads(context.read_bytes());pins={**c['pins_sha256'],**c['held_current_source_sha256']}
def guard():
 for n,h in pins.items():assert sha(R/n)==h,n
started=datetime.now(timezone.utc).isoformat();tick=time.perf_counter();guard();d=json.loads(request.read_bytes());assert sha(request)=='ceff089dd9ae990e3121674f1b8d28c9c80fe1773dc34c7e413748c82ff45b44';closed={str(request):sha(request),str(context):sha(context),str(Path(__file__)):sha(__file__)}
def add(q):
 if isinstance(q,dict):p=Path(q['file']);assert sha(p)==q['sha256'];h=q['sha256']
 else:p=Path(q);h=sha(p)
 assert str(p) not in closed or closed[str(p)]==h;closed[str(p)]=h;return ref(p)
add('/tmp/check-foundations-norm-csuses24-independent-applied28-v1.py');add('/tmp/foundations-norm-csuses24-independent-applied-actual28-v1.log');add('/tmp/foundations-norm-csuses24-independent-applied-reader1-failure-observation28-v1.json')
for k in ['complete_selected_dependencies','complete_primary_sources']:
 for q in d[k]:add(q)
add(d['actual_guard_context']);add(d['original_runner']);add(R/'SafeLearning/primer-linalg.html');add(R/'book/coverage/inventory.json');add(R/'book/coverage/foundations.json')
inv=json.loads((R/'book/coverage/inventory.json').read_bytes());material={u['key']:u for u in inv['material_source_units']}
for u in d['entire_literal_units']:assert material[u['key']]==u
page=(R/'SafeLearning/primer-linalg.html').read_text();assert d['full_literal_context']['text']=='\n'.join(page.splitlines()[119:182])
assert 'without subscript is the Euclidean norm' in page
history=[];components=[]
for g in d['groups']:
 add(g['proof_source']);s=Path(g['proof_source']['file']).read_text();assert s==g['entire_proof_source'];names=re.findall(r'^theorem\s+(\w+)',s,re.M);assert names==[n.split('.')[-1] for n in g['public_theorem_names']] and len(names)==g['public_theorem_count'];assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',s)
 actuals=g['actual_native_trials_and_failures'];assert len(actuals)==4
 for i,a in enumerate(actuals):
  for key in ['actual','source_snapshot','raw_log']:add(a[key])
  native=json.loads(Path(a['actual']['file']).read_bytes());assert type(native['actual_exit_code']) is int and native['actual_exit_code']==a['actual_exit_code']==(0 if i==3 else 1);assert native['protection_errors']==[];assert native['source_sha256_before']==native['source_sha256_after']==a['source_snapshot']['sha256']==native['source_snapshot_sha256'];assert native['raw_log_sha256']==a['raw_log']['sha256'];assert a['started_at_utc']==native['started_at_utc'] and a['finished_at_utc']==native['finished_at_utc'];warnings=len(re.findall(r'^.*:\d+:\d+: warning:',Path(a['raw_log']['file']).read_text(),re.M));assert warnings==a['actual_warning_count']
  history.append({'actual':a['actual'],'snapshot':a['source_snapshot'],'raw':a['raw_log'],'actual_exit_code':a['actual_exit_code'],'actual_warning_count':warnings,'started_at_utc':a['started_at_utc'],'finished_at_utc':a['finished_at_utc'],'body_and_time_preserved':True})
 assert actuals[-1]['source_snapshot']['sha256']==g['proof_source']['sha256']
 for name in g['public_theorem_names']:components.append({'name':name,'proof_source':g['proof_source'],'decision':'approved_exact_statement_and_complete_body','missing_clauses':[]})
assert len(components)==24
unitrows=[]
for u in d['entire_literal_units']:
 k=u['key'];approved=k!='primer-linalg.html::node-141'
 if approved:
  reason='All exact finite p>=1 norm formulas/axioms, one-norm nonnegative sum and norm unit-ball definition are supplied; the infinity maximum uses the ordinary positive finite coordinate dimension, with an explicit Nonempty index witness. The example and all diamond/disc/square equalities, nesting, convexity and symmetry are proved.'
  missing=[]
 else:
  reason='Every displayed mathematical route is proved for Euclidean vector norms fixed by page notation: disturbance CS, actual attained actuator support, distinct-class contrast norm and true Lipschitz margin transfer, arbitrary inverse-SPD inner form and CPO qs>=r^2. Current literal omits the two necessary support/contrast domains.'
  missing=[{'clause':'actuator support maximum','reason':'Require umax>=0. For a negative radius the ball is empty, so there is no attained maximum.'},{'clause':'norm of e_y-e_j equals sqrt2','reason':'Require j!=y. For j=y this vector is zero and its norm is zero.'}]
 unitrows.append({'key':k,'whole_unit_approved':approved,'decision':'approved_whole_exact_literal_under_explicit_context' if approved else 'pending_whole_exact_literal_two_qualifiers','source_text':u['source_text'],'text_sha256':u['text_sha256'],'source_sha256':u['source_sha256'],'hypotheses':['Finite real coordinate vectors; unadorned vector norms are Euclidean by page notation.','p>=1 for p-norm; positive finite coordinate dimension for an attained coordinate maximum.']+(['Actuator radius umax>=0 and competitor j!=y are explicit proof hypotheses; current unqualified literal remains pending.'] if not approved else []),'reason':reason,'missing_clauses':missing})
findings={'status':'passed_independent_full_norm_csuses24_source_component_and_literal_review','reviewer':'/root/applied_next','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(request),'components':components,'material_units':unitrows,'full24_proof_bodies_read':True,'all6_complete_selected_dependency_bodies_read':True,'primary_scope_read':'Complete Analysis.Matrix.PosDef and Normed.Module.Convex files; exact PiLp norm definitions/normed instances and used p/1/infinity formulas, and exact Matrix.PosDef inverse and Cauchy-Schwarz bodies. Complete primary files rehashed; no claim every unrelated lemma was semantically reread.','all8_genuine_native_trials_exact':history,'whole141_requires_reserved_source64_qualifiers':True,'prospective64_parser_or_source_application_claimed':False,'no_canonical_owner_source_or_compiler_mutation':True,'closed_evidence_sha256':closed,'errors':[]}
out=Path('/tmp/foundations-norm-csuses24-independent-applied-findings28-v2.json');assert not out.exists();out.write_text(json.dumps(findings,indent=2,ensure_ascii=False)+'\n');guard()
actual=Path('/tmp/foundations-norm-csuses24-independent-applied-actual28-v2.json');assert not actual.exists();actual.write_text(json.dumps({'status':'passed_actual_independent_readonly_norm_csuses24_review','actual_exit_code':0,'actual_command':['python3',str(Path(__file__))],'actual_workdir':str(R),'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.perf_counter()-tick,'helper_sha256_before':{str(Path(__file__)):sha(__file__)},'helper_sha256_after':{str(Path(__file__)):sha(__file__)},'findings':ref(out),'protection_errors':[],'protected_selected28_sources':1186,'protected_current60_assets':31,'protected_owner28_ledgers':5},indent=2)+'\n');print(json.dumps({'findings':ref(out),'actual':ref(actual),'components':len(components)}))
