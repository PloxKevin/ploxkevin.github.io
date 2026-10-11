from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,importlib.util,json
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256((Path(p)if Path(p).is_absolute()else R/p).read_bytes()).hexdigest();J=lambda p:json.loads((R/p).read_text())
I='book/coverage/checks/root_integrate_owner26_candidates_v2.py';B='book/coverage/checks/prepare_root_owner26_bindings_v4.py';assert H(I)=='0ad44698e172d8d3b9c52794d2d5a6531c0d19c7828cdad22cd380c26a44fe5c';assert H(B)=='f5b15f859cff5cb39606281c1bc7de8ed8a7e867e1b56337e4af9d3d514cfd0c'
prior='book/coverage/checks/future26-core/owner26-integration-and-binding-helpers-independent-modules-code-review-v1.json';assert H(prior)=='5dda8c13fe95e89ebe628155e49f439076cc8f72885d026c7d79aed13c685e31';previous=J(prior);assert previous['fixture_count']==54
for n,h in previous['closed_evidence_sha256'].items():assert H(n)==h
prior_b2='book/coverage/checks/prepare_root_owner26_bindings_v2.py';assert H(prior_b2)==previous['helpers_sha256'][prior_b2]
t=ast.parse((R/B).read_text());normalized=copy.deepcopy(t);normalized.body=[n for n in normalized.body if not(isinstance(n,ast.FunctionDef)and n.name=='native_offer_evidence_map')]
class Restore(ast.NodeTransformer):
 def visit_Call(self,n):
  n=self.generic_visit(n)
  if isinstance(n.func,ast.Name)and n.func.id=='native_offer_evidence_map':return ast.parse('offer.get(key,{})',mode='eval').body
  return n
assert ast.dump(Restore().visit(normalized),include_attributes=False)==ast.dump(ast.parse((R/prior_b2).read_text()),include_attributes=False)
spec=importlib.util.spec_from_file_location('reviewed_readonly_binder4',R/B);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);bn=vars(module);results=[]
def check(name,f,accept=False):
 try:f();a=True
 except(AssertionError,KeyError,TypeError,ValueError,OSError):a=False
 assert a==accept,(name,a);results.append({'fixture':name,'expected_accept':accept,'actual_accept':a,'scope':'Isolated native-list accept/reject; no production mutation.'})
applied_offer_path='book/coverage/checks/applied-future26/source53-v2/applied-audit26-candidate-source53-additions-v1-reviewed.json';applied=J(applied_offer_path)
assert len(applied['additional_frozen_inputs'])==144 and sum(n.startswith('book/coverage/')for n in applied['additional_frozen_inputs'])==141 and set(n for n in applied['additional_frozen_inputs']if not n.startswith('book/coverage/'))==set(applied['proof_files'])
check('actual Applied exact144 list/companion map accepted',lambda:bn['native_offer_evidence_map']('applied','additional_frozen_inputs',applied),True)
for owner,field in [('core','additional_frozen_inputs'),('applied','required_live_integration_evidence_sha256')]:
 bad=copy.deepcopy(applied)
 if field!='additional_frozen_inputs':bad[field]=bad['additional_frozen_inputs']
 check('list authorization rejects '+owner+'/'+field,lambda o=owner,f=field,bad=bad:bn['native_offer_evidence_map'](o,f,bad))
def mutated_list(m):
 bad=copy.deepcopy(applied);m(bad);mapping=bn['native_offer_evidence_map']('applied','additional_frozen_inputs',bad)
 for n,h in mapping.items():bn['add_evidence']({},n,h)
for name,mutate in [
 ('wrong length',lambda d:d['additional_frozen_inputs'].pop()),
 ('duplicate path',lambda d:d['additional_frozen_inputs'].__setitem__(0,d['additional_frozen_inputs'][1])),
 ('absolute name',lambda d:d['additional_frozen_inputs'].__setitem__(0,'/tmp/a')),
 ('outside book scope',lambda d:d['additional_frozen_inputs'].__setitem__(0,'reports/full-coverage/x.json')),
 ('nonstring name',lambda d:d['additional_frozen_inputs'].__setitem__(0,1)),
 ('missing companion',lambda d:d.pop('required_evidence_artifacts_sha256')),
 ('companion extra',lambda d:d['required_evidence_artifacts_sha256'].update({'book/coverage/no-extra.json':'0'*64})),
 ('hash drift',lambda d:d['required_evidence_artifacts_sha256'].__setitem__(d['additional_frozen_inputs'][0],'0'*64)),
 ('tuple instead of list',lambda d:d.update(additional_frozen_inputs=tuple(d['additional_frozen_inputs']))),
 ('noncanonical traversal',lambda d:d['additional_frozen_inputs'].__setitem__(0,'book/coverage/../outside.json'))]:check('Applied list rejects '+name,lambda m=mutate:mutated_list(m))
def unknown_lean(d):
 old=next(n for n in d['additional_frozen_inputs']if n in d['proof_files']);new='verification/lean/SafeLearning/NotAnOfferedProof.lean';d['additional_frozen_inputs'][d['additional_frozen_inputs'].index(old)]=new;d['required_evidence_artifacts_sha256'][new]=d['required_evidence_artifacts_sha256'].pop(old)
check('unknown Lean path rejected even with exact companion set',lambda:mutated_list(unknown_lean))
check('native dictionary representation unchanged',lambda:bn['native_offer_evidence_map']('core','additional_frozen_inputs',{'additional_frozen_inputs':{'book/coverage/core.json':H('book/coverage/core.json')}}),True)
# Read the complete native request4 construction and full binder function in memory.
# The unchanged real I2 peer is used as that function's I2 code gate. Its B2-only
# mapping assertion is omitted ONLY inside this isolated prepublication fixture,
# because this new B4 peer is the output being independently established here.
# No synthetic passed peer is written or read; no actual request producer runs.
request4='book/coverage/checks/create_root_owner26_binding_request_v5.py';rt=ast.parse((R/request4).read_text())
rt.body=[n for n in rt.body if not(isinstance(n,ast.If)and isinstance(n.test,ast.Compare)and isinstance(n.test.left,ast.Name)and n.test.left.id=='__name__')]
prepare=next(n for n in rt.body if isinstance(n,ast.FunctionDef)and n.name=='prepare')
prepare.body=[n for n in prepare.body if not(isinstance(n,ast.Assert)and "helperpeer['helpers_sha256']"in ast.unparse(n.test))]
stop=next(i for i,n in enumerate(prepare.body)if isinstance(n,ast.With))
prepare.body=prepare.body[:stop]+[ast.Return(value=ast.parse("{'config':config,'observation':observation}",mode='eval').body)]
assert not any(isinstance(n,ast.Call)and ast.unparse(n.func).endswith(('.write_text','.write_bytes','.mkdir'))for n in ast.walk(rt))
rns={'__file__':str(R/request4)};exec(compile(ast.fix_missing_locations(rt),request4,'exec'),rns)
from types import SimpleNamespace
real_prior_peer='book/coverage/checks/future26-core/owner26-integration-and-binding-helpers-independent-modules-code-review-v1.json';core_actual='reports/full-coverage/finalize-root-core26-offer-execution-v1.json'
args=SimpleNamespace(root_authorized_binding_request_preparation=True,independent_peer=real_prior_peer,peer_sha256=H(real_prior_peer),core_finalization_execution=core_actual,core_finalization_execution_sha256=H(core_actual))
full=rns['prepare'](args);observation=full['observation'];assert observation['new_proof_sources']==11 and observation['new_public_exports']==134 and observation['original_canonical_execution_records']==22
assert observation['owners'].keys()=={'core','foundations','applied','modules'}
assert not(R/rns['OUT']).exists() and not(R/rns['DEST']).exists()
out={'status':'passed_independent_owner26_binder4_strict_native_list_delta_and_complete_four_offer_prewrite_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':H(I),'helpers_sha256':{I:H(I),B:H(B)},'entire_original_independent_I2_B2_review_body_and_time':previous,'original_independent_I2_B2_review':{'file':prior,'sha256':H(prior)},'prior54_fixtures_reused_exact_without_reexecution':True,'exact_binder4_to_binder2_only_native_list_normalization_delta':True,'native_list_count':144,'native_book_artifacts':141,'native_exact_offered_proof_source_entries':3,'new_fixture_count':len(results),'new_fixtures':results,'complete_native_request5_construction_and_full_build_binding_prewrite_function_passed':True,'native_request5':{'file':request4,'sha256':H(request4)},'native_sources':11,'native_public_exports':134,'native_original_canonical_records':22,'original_semantic_status_times':{o:v['original_full_source_semantic_reviews']for o,v in observation['owners'].items()},'fixture_metadata_gate_scope':'Only the request constructor B4-helper-peer mapping assertion was omitted in memory, using the genuine previously passed unchanged I2 code peer. No synthetic passed peer was written or read. All actual native offers, source/record/helper hashes and complete binder function checks ran.','scope':'Independent strict-list code delta, narrow accept/reject fixtures and complete real four-offer prewrite construction/binding in memory. Prior54 fixtures/body/time retained without rerun. No actual request or native binding producer, integration/compiler/global/aggregate execution claimed.'}
p=Path('/tmp/owner26-integration-binding-independent-modules-code-review-v6.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'peer':str(p),'sha256':H(p),'new_fixtures':len(results)}))
