from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');I='book/coverage/checks/root_integrate_owner26_candidates_v2.py';B='book/coverage/checks/prepare_root_owner26_bindings_v2.py';H=lambda p:hashlib.sha256((Path(p)if Path(p).is_absolute()else R/p).read_bytes()).hexdigest();J=lambda p:json.loads((R/p).read_text())
assert H(I)=='0ad44698e172d8d3b9c52794d2d5a6531c0d19c7828cdad22cd380c26a44fe5c';assert H(B)=='eb5f056ad388cbaff8edbd9ad144bac26a09208cfd6b280712934808765b498b'
oldi=R/'book/coverage/checks/root_integrate_owner26_candidates_v1.py';s=(R/I).read_text();assert ast.dump(ast.parse(s.replace('    assert str(name) == original_name\n','').replace('    original_name = name\n','')))==ast.dump(ast.parse(oldi.read_text()))
oldb=(R/'book/coverage/checks/prepare_root_owner26_bindings_v1.py').read_text();sb=(R/B).read_text();rev=sb.replace("('actual_workdir', 'cwd', 'working_directory')","('actual_workdir', 'cwd')").replace('root_integrate_owner26_candidates_v2.py','root_integrate_owner26_candidates_v1.py').replace(H(I),H(oldi));assert ast.dump(ast.parse(rev))==ast.dump(ast.parse(oldb))
def functions(p):
 t=ast.parse((R/p).read_text());nodes=[]
 for n in t.body:
  if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef)):nodes.append(n)
  elif isinstance(n,ast.Assign)and all(isinstance(x,ast.Name)for x in n.targets)and not any(isinstance(x,ast.Call)and isinstance(x.func,ast.Attribute)and isinstance(x.func.value,ast.Name)and x.func.value.id=='arguments'for x in ast.walk(n)):
   if any(isinstance(x,ast.Name)and x.id in ['args','binding','manifest','assets','source53','source53_execution','selection','snapshot','report_name','original25_assets','allowed_destinations','untouched_working','archive_name']for x in n.targets):continue
   nodes.append(n)
 ns={'__file__':str(R/p)};exec(compile(ast.Module(body=nodes,type_ignores=[]),p,'exec'),ns);return ns
bn=functions(B);it=functions(I);results=[]
def check(name,f,accept=False):
 try:f();a=True
 except(AssertionError,KeyError,TypeError,ValueError):a=False
 assert a==accept,(name,a);results.append({'fixture':name,'expected_accept':accept,'actual_accept':a,'scope':'Isolated read-only function invocation; no integration/binding production.'})
for modname,mod in [('I2',it),('B2',bn)]:
 check(modname+' true int0',lambda m=mod:m['zero']({'actual_exit_code':0,'exit_code':0}),True)
 for n,d in [('boolFalse',{'actual_exit_code':False}),('float0',{'actual_exit_code':0.0}),('string0',{'actual_exit_code':'0'}),('nonzero',{'actual_exit_code':1}),('conflict',{'actual_exit_code':0,'exit_code':1}),('missing',{})]:check(modname+' rejects '+n,lambda m=mod,d=d:m['zero'](d))
for name in ['','.', './book/coverage/core.json','book//coverage/core.json','../outside','/tmp/x']:
 for mod,fn in [(it,'safe_path'),(bn,'safe')]:check(fn+' rejects '+repr(name),lambda m=mod,f=fn,n=name:m[f](n))
for mod,fn in [(it,'safe_path'),(bn,'safe')]:check(fn+' canonical',lambda m=mod,f=fn:m[f]('book/coverage/core.json'),True)
for n,r,keys in [('command conflict',{'command':['a'],'actual_command':['b']},('command','actual_command')),('log digest conflict',{'log_sha256':'a','raw_log_sha256':'b'},('log_sha256','raw_log_sha256')),('workdir conflict',{'actual_workdir':str(R),'working_directory':'/tmp'},('actual_workdir','cwd','working_directory')),('missing alias',{},('command','actual_command'))]:check(n,lambda r=r,k=keys:bn['alias'](r,k))
builders=['book/coverage/checks/foundations-future26/source53/foundations26-source53-identity-builder-actual-execution-v1.json','book/coverage/checks/applied-future26/source53-v2/source53-identity-preparation-actual-v2.json','book/coverage/checks/modules-future26/source53/modules26-source53-identity-builder-actual-v1.json','reports/full-coverage/root-core26-composed-candidate-execution-v2.json']
for p in builders:check('native actual builder '+p,lambda p=p:bn['actual_builder_evidence'](J(p)),True)
proofs={}
for p in ['book/coverage/checks/foundations-future26/source53/foundations-audit26-candidate-source53-additions-v1-reviewed.json','book/coverage/checks/modules-future26/source53/modules-audit26-candidate-source53-additions-v1-reviewed.json','book/coverage/checks/applied-future26/source53-v2/applied-audit26-candidate-source53-additions-draft-v1.json']:proofs.update(J(p)['proof_files'])
def collect(v,d):
 if isinstance(v,dict):
  if isinstance(v.get('file'),str)and isinstance(v.get('sha256'),str)and not Path(v['file']).is_absolute():d[v['file']]=v['sha256']
  for x in v.values():collect(x,d)
 elif isinstance(v,list):
  for x in v:collect(x,d)
c=J('book/coverage/checks/future26-core/composed-source53-v3/core26-source53-composed-candidate-v1.json')
for row in c['future26_composed_candidate_binding']['new_proof_sources']:
 e={};collect(J(row['readiness']['file']),e);collect(row,e)
 for pair in row['pair']:
  d=J(pair.get('record',pair)['file']);log=d.get('log',d.get('raw_log'));e[log]=H(log)
 proofs[row['source']['file']]={'sha256':row['source']['sha256'],'evidence_sha256':e}
assert len(proofs)==11
native_pairs={}
for p,row in proofs.items():
 r=bn['canonical_pair'](p,row);assert len(r['actual_pair'])==2;native_pairs[p]=r;check('native canonical pair '+Path(p).name,lambda p=p,row=row:bn['canonical_pair'](p,row),True)
source=next(iter(proofs));proof=proofs[source];pair=native_pairs[source]['actual_pair'][0]['file'];native_read=bn['read'];native_sha=bn['sha']
def mutated_pair(mutate):
 def read(p):
  d=native_read(p)
  if p==pair:mutate(d)
  return d
 bn['read']=read
 try:bn['canonical_pair'](source,proof)
 finally:bn['read']=native_read
check('canonical bool exit rejected',lambda:mutated_pair(lambda d:d.update(exit_code=False,actual_exit_code=False)))
check('canonical command aliases conflict rejected',lambda:mutated_pair(lambda d:d.update(actual_command=['wrong'])))
check('canonical log aliases conflict rejected',lambda:mutated_pair(lambda d:d.update(raw_log_sha256='0'*64)))
check('canonical source false rejected',lambda:mutated_pair(lambda d:d.update(source_unchanged=False)))
check('canonical wrong workdir rejected',lambda:mutated_pair(lambda d:d.update(actual_workdir='/tmp')))
# Removing either required native pair rejects, while no temporary absolute command is inferred as canonical.
for kind in [0,1]:
 p=native_pairs[source]['actual_pair'][kind]['file'];bad=copy.deepcopy(proof);bad['evidence_sha256'].pop(p);check('missing pair '+str(kind),lambda bad=bad:bn['canonical_pair'](source,bad))
assert 'authorized_current_future_code_updates'not in s and 'authorized_current_future_code_updates'not in sb
assert "assert len(seen_new_proofs) == binding[\"new_proof_sources\"] == 11"in s
assert 'all44111_frozen25_inputs_exact' in s and 'original25_byte_copy' in s
assert s.count('verify_frozen_and_sources()')==3 and 'os.replace(temporary, original)'in s
out={'status':'passed_independent_owner26_integration_and_binding_code_and_native_schema_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':H(I),'helpers_sha256':{I:H(I),B:H(B)},'exact_narrow_inverse_to_unexecuted_v1_drafts':True,'original_v1_read_findings':['I1 did not reject noncanonical path spelling accepted by Path normalization.','B1 did not recognize native Applied53 working_directory; B2 adds it as a strict agreeing alias.'],'native_sources':11,'native_original_canonical_records':22,'native_actual_builder_records':builders,'native_pairs':native_pairs,'fixture_count':len(results),'fixtures':results,'no_historical_future_code_exception':True,'baseline25_manifest':{'file':'reports/full-coverage/checkpoint-25-manifest.json','sha256':'0329596719e09459730f34c9c84e9bacf4f3698a7c1699c4f848cef975ee5363'},'current_inventory53_sha256':'4b1e657eb61234a6d2e2a3a3ea6a0b11986c01d7d1c7cb5ba2dd5452d1fe29be','scope':'Full code/delta read and isolated guard/native-schema fixtures. All eleven actual proof pairs and four genuine candidate builder schemas read. No complete four-offer production binding/dry/apply/install/global/aggregate execution claimed; Root must separately execute those gates.'}
p=Path('/tmp/owner26-integration-binding-independent-modules-code-review-v1.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':str(p),'sha256':H(p),'fixture_count':len(results)}))
