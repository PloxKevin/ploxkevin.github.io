from pathlib import Path
from datetime import datetime,timezone
import importlib.util,sys,json,hashlib,copy,shutil
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');O=Path('/tmp/optimization-source62-independent-modules28-v1');assert not O.exists();O.mkdir()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p)}
def read(p):return json.loads(Path(p).read_bytes())
request_path=Path('/tmp/optimization-timing-relu-source62-proposal28-v1/optimization-timing-relu-source62-independent-review-request28-v1.json');request=read(request_path)
def pin(q):
 p=Path(q['file']);p=p if p.is_absolute() else R/p
 assert sha(p)==q['sha256'],str(p)
 return p
for k,v in request.items():
 if isinstance(v,dict)and set(v)>={'file','sha256'}:pin(v)
packet_path=pin(request['proposal']);packet=read(packet_path)
for k in ['before_inventory','before_corrections','source','parser','proposed_source','proposed_full29_inventory','original_owner_at_author_read','explicit_countermodel_and_parameter_image_draft']:
 pin(packet[k])
for row in packet['primary_mathlib_api_files']:pin(row)
# Original body/time remains bound by the original author native bytes.
native_path=pin(request['actual_preparation']);native=read(native_path);assert native['status']=='passed'and native['actual_exit_code']==0 and native['protection_errors']==[]
assert sha(Path(native['raw_log']))==native['raw_log_sha256']
assert native['checker_sha256_before']==native['checker_sha256_after']==request['helper']['sha256']
assert native['actual_command']==['python3',request['helper']['file']]
for k in ['started_at_utc','finished_at_utc','elapsed_seconds']:assert k in native
source=pin(packet['source']);proposed=pin(packet['proposed_source']);old=source.read_text();new=proposed.read_text();inv=read(pin(packet['before_inventory']));expectedkeys=['primer-optimization.html::node-200','primer-optimization.html::node-202']
assert request['countermodel_draft_compiled']is False and packet['countermodel_draft_compiled']is False
assert request['whole_coverage_requested']is False and request['source_application_requested']is False
assert packet['whole_material_or_exercise_approved']is False and packet['canonical_source_owner_compiler_publication_mutation_claimed']is False
assert packet['prospective_source_batch']==62
sys.path.insert(0,str(R/'book'));from validate import Document
replacements=packet['exact_replacements'];assert len(replacements)==3
def exact_source(after):
 rebuilt=old
 for row in replacements:
  assert rebuilt.count(row['before'])==1 and row['after']not in rebuilt
  rebuilt=rebuilt.replace(row['before'],row['after'],1)
 assert after==rebuilt
 reverse=after
 for row in reversed(replacements):
  assert reverse.count(row['after'])==1
  reverse=reverse.replace(row['after'],row['before'],1)
 assert reverse.encode()==source.read_bytes()
 a=Document(old);b=Document(after);assert [(n.tag,n.attrs,n.line)for n in a.nodes]==[(n.tag,n.attrs,n.line)for n in b.nodes]
 assert old.count('\n')==after.count('\n')
exact_source(new)
assert packet['full_current_context_lines165_to189']==''.join(old.splitlines(keepends=True)[164:189])
assert packet['full_proposed_context_lines165_to189']==''.join(new.splitlines(keepends=True)[164:189])
owner_snapshot=read(pin(packet['original_owner_at_author_read']));current_owner=read(R/'book/coverage/foundations.json')
for k in expectedkeys:
 rows=[x for x in owner_snapshot['material_claims']if k in x.get('source_unit_keys',[])];assert rows==packet['original_owner_claim_rows_body_and_time'][k]
 assert rows==[x for x in current_owner['material_claims']if k in x.get('source_unit_keys',[])],('current owner clause changed',k)
 assert all(x['status']=='pending'and x['lean_declarations']==[]for x in rows)
parser_path=pin(packet['parser']);isolation=O/'independent-isolated-full29';(isolation/'SafeLearning').mkdir(parents=True)
for page in sorted((R/'SafeLearning').glob('*.html')):
 dest=isolation/'SafeLearning'/page.name;dest.write_bytes(proposed.read_bytes()if page==source else page.read_bytes())
assert len(list((isolation/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('source62_independent_modules_parser_v1',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser);parser.ROOT=isolation;parser.OUT=isolation/'book/coverage'
def require_isolated(root,out):
 assert root.resolve().is_relative_to(O.resolve())and out.resolve().is_relative_to(O.resolve())
 assert root.resolve()!=R.resolve()and out.resolve()!=(R/'book/coverage').resolve()
require_isolated(parser.ROOT,parser.OUT);parser.inventory();fresh=read(parser.OUT/'inventory.json');author=read(pin(packet['proposed_full29_inventory']))
assert fresh['counts']==author['counts']==inv['counts'];assert fresh['source_sha256']==author['source_sha256']=={**inv['source_sha256'],'SafeLearning/primer-optimization.html':sha(proposed)}
changes={}
for field in ['exercises','material_source_units']:
 assert fresh[field]==author[field]
 a={v['key']:v for v in inv[field]};b={v['key']:v for v in fresh[field]};assert a.keys()==b.keys();changes[field]=[]
 for k in a:
  x=copy.deepcopy(a[k]);y=copy.deepcopy(b[k])
  if x['source']=='SafeLearning/primer-optimization.html':
   assert y['source_sha256']==sha(proposed);x.pop('source_sha256');y.pop('source_sha256')
  if x!=y:
   assert {n:v for n,v in x.items()if n not in ['source_text','text_sha256']}=={n:v for n,v in y.items()if n not in ['source_text','text_sha256']}
   changes[field].append(k);assert packet['entire_changed_material_records'][k]=={'entire_original_inventory_record':a[k],'entire_proposed_inventory_record':b[k]}
assert changes=={'exercises':[],'material_source_units':expectedkeys}
negatives=[]
def reject(label,fn):
 try:fn()
 except(AssertionError,KeyError,ValueError):negatives.append({'fixture':label,'rejected':True});return
 raise AssertionError('Accepted negative fixture '+label)
for index,label in enumerate(['remove_full_parameter_interval_coverage','remove_activation_differentiability_qualifier','remove_output_switch_cancellation_qualification']):
 reject(label,lambda index=index:exact_source(new.replace(replacements[index]['after'],replacements[index]['before'],1)))
reject('alter_unchanged_numeric_backprop_example',lambda:exact_source(new.replace('$x=(1,0.25)$','$x=(1,0.5)$',1)))
reject('alter_unchanged_oscillator_example',lambda:exact_source(new.replace('$(0.6,0.8)$','$(0.6,0.9)$',1)))
reject('add_unreviewed_fourth_prose_change',lambda:exact_source(new.replace('Definition &mdash; Hessian','Definition &mdash; Modified Hessian',1)))
reject('insert_newline_changes_literal_node_lines',lambda:exact_source(new+'\n'))
reject('change_existing_html_node_attribute',lambda:exact_source(new.replace('id="opt-chain-rule"','id="opt-chain-rule-changed"',1)))
reject('parser_ROOT_live_writes_disallowed',lambda:require_isolated(R,parser.OUT))
reject('parser_OUT_live_writes_disallowed',lambda:require_isolated(parser.ROOT,R/'book/coverage'))
# Scope metadata is checked explicitly: no compiled draft or whole/source approvals.
def check_scope(req,pack):
 assert req['countermodel_draft_compiled']is False and pack['countermodel_draft_compiled']is False
 assert req['whole_coverage_requested']is False and req['source_application_requested']is False
 assert pack['whole_material_or_exercise_approved']is False
for key in ['countermodel_draft_compiled','whole_coverage_requested','source_application_requested']:
 bad=copy.deepcopy(request);bad[key]=True;reject('invent_'+key,lambda bad=bad:check_scope(bad,packet))
# Model has read full two literal records, both full contexts, all unchanged calculations, pending clauses and the entire uncompiled draft.
result={'status':'passed_independent_narrow_source62_timing_activation_and_cancellation_wording_and_isolated29_parser_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'proposal':ref(packet_path),'request':ref(request_path),'original_author_native':ref(native_path),'original_author_native_body_and_time_unchanged':True,'original_author_log':request['actual_preparation_log'],'source':packet['source'],'proposed_source':packet['proposed_source'],'before_inventory':packet['before_inventory'],'before_corrections':packet['before_corrections'],'independent_isolated_parser_inventory':ref(parser.OUT/'inventory.json'),'isolated_ROOT':str(parser.ROOT),'isolated_OUT':str(parser.OUT),'both_ROOT_and_OUT_isolated':True,'changed_text_keys':changes,'counts':fresh['counts'],'full_nodes_tag_attr_line_identity_preserved':True,'exact_three_substitution_forward_and_byte_reverse':True,'full_literal_and_context_read':True,'negative_fixtures':negatives,'semantic_decisions':[{'clause':'node200 time scaling','approved':True,'reason':'A differentiable constant timing s=0 has nonnegative derivative while its path image is only q(0). Nonnegative derivative preserves parameter order on the differentiable time interval; coverage of the full [0,1] parameter interval supplies equality of images. Derivative zero is stated only as instantaneous stopping. Displayed first/second derivative formulas and oscillator arithmetic are unchanged.'},{'clause':'node202 backprop domain','approved':True,'reason':'The ordinary activation chain rule applies when every scalar activation is differentiable at its preactivation. The printed example has both preactivations positive, so its v=(1.5,.5), gradient=(2,0), and local f=2x1 calculation are unchanged.'},{'clause':'node202 possible output nondifferentiability','approved':True,'reason':'Finite ReLU compositions are continuous piecewise affine. A zero/nonzero sign boundary for a nonconstant affine preactivation is a proper hyperplane piece; identically zero tests create no switching face. Output nondifferentiability can occur only on finitely many such pieces, which have Lebesgue measure zero. Identical neurons with output weights1,-1 cancel to the differentiable zero function, so no universal nondifferentiability claim remains. An autodiff convention at zero remains explicitly a convention.'}],'countermodel_draft':request['countermodel_draft'],'countermodel_draft_compiled':False,'no_lean_kernel_result_inferred':True,'whole_node200_approved':False,'whole_node202_approved':False,'pending_full_scope':packet['preserved_pending_scope'],'source62_reserved_by_Root_later_message_original_proposal_reserved_flag_retained':True,'source62_applied':False,'production_source_owner_selection_freeze_publication_changes':False,'durable_bookcoverage_closure_deferred_until_root_freeze_completion':True,'coverage_complete':False}
out=O/'optimization-source62-independent-modules-peer-v1.json';out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'peer':ref(out),'negative_fixture_count':len(negatives),'changes':changes,'whole_coverage_approved':False}))
