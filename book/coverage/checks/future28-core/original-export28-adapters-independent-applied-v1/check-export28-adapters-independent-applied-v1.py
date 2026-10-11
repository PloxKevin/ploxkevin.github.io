from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref=lambda p:{'file':Path(p).relative_to(R).as_posix() if Path(p).is_relative_to(R) else str(p),'sha256':H(p)}
E=R/'book/coverage/export_audit28_v1.py';I=R/'book/coverage/checks/root_check_export28_integrity_v1.py'
PE=R/'book/coverage/export_audit27_v3.py';PI=R/'book/coverage/checks/root_check_export27_integrity_v1.py'
assert H(E)=='9402d0c0d89ed910c783a1a406fcaea90f751371e3edbe30fda8caca2c05b9e1'
assert H(I)=='a7e2583feccdc7986b279d71b98f8a4482804c8b86f60141fef4be63f1056616'
start=datetime.now(timezone.utc).isoformat();ec=E.read_text();ic=I.read_text()
assert ec.replace('checkpoint-28','checkpoint-27').replace('1186','1175').replace('9896','9644')==PE.read_text()
assert ic.replace('fresh==11 and reused==1175','fresh==8 and reused==1167').replace('1186','1175').replace('9896','9644').replace('checkpoint-28','checkpoint-27')==PI.read_text()
ast.parse(ec);ast.parse(ic)
before={p:H(p) for p in (E,I,PE,PI)}
cases=[]
def yes(name,fn):fn();cases.append({'name':name,'result':'accepted'})
def no(name,fn):
    try:fn()
    except (AssertionError,ValueError,KeyError,TypeError):cases.append({'name':name,'result':'rejected'})
    else:raise AssertionError('Unexpected acceptance '+name)
exportgates=ec[ec.index("assert isinstance(report['checks']"):ec.index("for field in ['source_sha256'")]
exportgates=exportgates.replace("manifest_path = snapshot.parent / (snapshot.name + '-manifest.json')\nmanifest = json.loads(manifest_path.read_text())\n",'')
proofs={f'synthetic/proof-{i}.lean':'a'*64 for i in range(1186)}
decls=[{'name':f'Synthetic.decl{i}'} for i in range(9896)]
report={'checks':[{'exit_code':0}], 'status':'passed','proof_file_count':1186,'proof_sha256':proofs,'theorem_count':9896,'declarations':decls,'axiom_dependencies':{d['name']:['propext','Classical.choice','Quot.sound'] for d in decls},'allowed_standard_axioms':['propext','Classical.choice','Quot.sound']}
manifest={'proof_files':{n:{'sha256':h} for n,h in proofs.items()}}
def exportgate(r,m=manifest):exec(exportgates,{'report':r,'manifest':m})
yes('synthetic current28 1186/9896 gate only',lambda:exportgate(report))
for name,r in [('old1175 file count',{**report,'proof_file_count':1175}),('old9644 theorem count',{**report,'theorem_count':9644}),('empty checks',{**report,'checks':[]}),('missing proof hash',{**report,'proof_sha256':dict(list(proofs.items())[1:])}),('pending aggregate',{**report,'status':'pending'}),('false success code',{**report,'checks':[{'exit_code':False}]}),('float success code',{**report,'checks':[{'exit_code':0.0}]}),('failed success code',{**report,'checks':[{'exit_code':1}]})]:no(name,lambda r=r:exportgate(r))
mm=copy.deepcopy(manifest);mm['proof_files'][next(iter(proofs))]['sha256']='b'*64
no('changed frozen selection map',lambda:exportgate(report,mm))
integritygates=ic[ic.index("assert original['status']"):ic.index('expected=copy.deepcopy(original)')]
def integritygate(r):exec(integritygates,{'original':r})
yes('synthetic complete declaration/axiom keys gate',lambda:integritygate(report))
r={**report,'declarations':decls[:-1]};no('missing declaration row',lambda:integritygate(r))
r={**report,'axiom_dependencies':dict(list(report['axiom_dependencies'].items())[1:])};no('missing axiom dependency key',lambda:integritygate(r))
r=copy.deepcopy(report);r['axiom_dependencies'].pop('Synthetic.decl0');r['axiom_dependencies']['Synthetic.other']=[];no('same count wrong declaration key',lambda:integritygate(r))
r=copy.deepcopy(report);r['axiom_dependencies']['Synthetic.decl0']=['sorryAx'];no('nonstandard axiom',lambda:integritygate(r))
freshgate=ic[ic.index("fresh=sum("):ic.index('result.write_text')]
def replaygate(f,r):exec(freshgate,{'original':{'checks':[{'evidence_mode':'fresh_kernel_replay'}]*f+[{'evidence_mode':'reused_identical_module_and_transitive_local_imports'}]*r}})
yes('synthetic eleven fresh1175 exact reused gate',lambda:replaygate(11,1175));no('old eight fresh',lambda:replaygate(8,1175));no('old1167 reused',lambda:replaygate(11,1167));no('twelve fresh',lambda:replaygate(12,1175))
tree=ast.parse(ec);node=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='relocate_check');ns={'old_prefix':'reports/lean-verification/','new_prefix':'reports/full-coverage/lean-checkpoint-28/'};exec(compile(ast.Module(body=[node],type_ignores=[]),str(E),'exec'),ns)
c={'output_file':'reports/lean-verification/new.log','reused_from':{'report':'reports/lean-verification/reused.json','original_check':{'output_file':'reports/lean-verification/old-historical.log','command':['lake','old-command'],'started_at_utc':'original historical time'}}};old=copy.deepcopy(c['reused_from']['original_check']);ns['relocate_check'](c)
assert c['output_file']=='reports/full-coverage/lean-checkpoint-28/new.log'and c['reused_from']['report']=='reports/full-coverage/lean-checkpoint-28/reused.json'and c['reused_from']['original_check']==old
cases.append({'name':'current paths relocate while whole historical check remains unchanged','result':'accepted'})
for p,h in before.items():assert H(p)==h
OUT=Path('/tmp/export28-adapters-independent-applied-reader-v1.json');assert not OUT.exists()
d={'status':'passed_independent_checkpoint28_export_and_integrity_adapter_delta_code_review','errors':[],'helpers':{'export':ref(E),'integrity':ref(I)},'review_started_at_utc':start,'review_finished_at_utc':datetime.now(timezone.utc).isoformat(),'exact_delta_reverses_to_original27_helpers':{'export':ref(PE),'integrity':ref(PI)},'fixtures':cases,'fixture_inputs_explicitly_synthetic':True,'expected_counts':{'proof_files':1186,'theorem_or_lemma_declarations':9896,'fresh_kernel_replays':11,'exact_original_kernel_replays_reused':1175},'whole_original_history_and_compact_serialization_preserved':True,'production28_audit_export_or_integrity_execution_claimed':False,'conditional_scope':'Full static adapter read, exact reverse to original27 code, and isolated actual gate/relocation fixtures. No frozen28 report or aggregate28 exists for this reviewer, and neither producer script was invoked. Root must run actual aggregate/export/integrity in order.','closed_evidence_sha256':{ref(p)['file']:H(p)for p in before}}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'reader':ref(OUT),'fixtures':len(cases)}))
