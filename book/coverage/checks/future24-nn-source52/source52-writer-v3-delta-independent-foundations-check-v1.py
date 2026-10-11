from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future24-nn-source52'
OLD=ROOT/'book/coverage/checks/root_source_batch52_v2.py';NEW=ROOT/'book/coverage/checks/root_source_batch52_v3.py'
OUT=BASE/'source52-writer-v3-delta-independent-foundations-review-v1.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
ref=lambda p:{'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
assert not OUT.exists() and H(OLD)=='84fa36f2b88b7ab7ecb06a70dbc200f14d58f4c50adb88193b2c18d79fe62b1f' and H(NEW)=='25ace4730a09aeed29c7024cc249d4d0b7649f47097a8092668edb97c33f3c4e'
priorp=BASE/'source52-writer-independent-foundations-review-v2.json';prior=read(priorp)
assert H(priorp)=='f4a4d5db00e603196af77392d10a60133d58f1761be3b20d9a855dec2a47721d' and 'passed' in prior['status'] and prior['errors']==[]
catalogp=BASE/'approved-source52-catalog-v1.json';c=read(catalogp)
assert H(catalogp)=='68ad4d6cb53c99e8a5721ae88cf16d1b88a6939773b61c897cf118ab107a6f31' and len(c['pages'])==1
item=c['pages'][0];proposal=read(ROOT/item['proposal'])
assert H(ROOT/item['proposal'])==item['proposal_sha256'] and len(item['proof_source_sha256'])==3
for name,digest in item['proof_source_sha256'].items():assert H(ROOT/name)==digest
trees=[ast.parse(p.read_text()) for p in [OLD,NEW]]
def mainloop(t):
 main=next(n for n in t.body if isinstance(n,ast.If))
 return next(n for n in main.body if isinstance(n,ast.For) and isinstance(n.target,ast.Tuple) and [x.id for x in n.target.elts]==['index','item'])
oldloop,newloop=[mainloop(t) for t in trees]
assert ast.unparse(oldloop.body[-1]).startswith('pages.append(dict(**item,')
assert ast.unparse(newloop.body[-3])=='page = dict(item)' and ast.unparse(newloop.body[-1])=='pages.append(page)'
normalized=copy.deepcopy(trees[0]);mainloop(normalized).body[-1:]=copy.deepcopy(newloop.body[-3:])
assert ast.dump(normalized)==ast.dump(trees[1]),'Changes beyond the exact corrected page assembly'
def assembly(body):
 env={'item':copy.deepcopy(item),'index':52,'source':proposal['source'],'H':H,'R':ROOT,
      'target_hash':proposal['proposed_source_sha256_after'],'proposal':copy.deepcopy(proposal),
      'proofs':copy.deepcopy(item['proof_source_sha256']),'pages':[]}
 exec(compile(ast.Module(body=body,type_ignores=[]),str(NEW),'exec'),env)
 return env
try:assembly([oldloop.body[-1]])
except TypeError as e:old_failure=str(e);assert 'proof_source_sha256' in old_failure and 'multiple values' in old_failure
else:raise AssertionError('Actual three-proof catalogue must demonstrate the original duplicate-key failure')
env=assembly(newloop.body[-3:]);assert len(env['pages'])==1 and env['item']==item
expected=copy.deepcopy(item)
expected.update({'correction_index':52,'source':proposal['source'],'before_sha256':H(ROOT/proposal['source']),
 'after_sha256':proposal['proposed_source_sha256_after'],'replacements':proposal['replacements'],
 'proof_source_sha256':item['proof_source_sha256']})
assert env['pages'][0]==expected and len(expected['proof_source_sha256'])==3
assert expected['before_sha256']==proposal['source_sha256_before'] and len(expected['replacements'])==2
assert {k:v for k,v in expected.items() if k in item and k not in ['proof_source_sha256']}=={k:v for k,v in item.items() if k!='proof_source_sha256'}
failp=ROOT/'reports/full-coverage/source52-dry-execution-v1.json';fail=read(failp)
assert fail['actual_exit_code']==1 and H(ROOT/fail['log'])==fail['log_sha256']=='cafce58723c4311e56bd4a78bd967b18fb880a5661f08090fd95cb8816f11ae4'
assert fail['helper_sha256_before']==fail['helper_sha256_after']=={str(OLD.relative_to(ROOT)):H(OLD)}
assert 'proof_source_sha256' in (ROOT/fail['log']).read_text()
aliap=BASE/'failed-root-dry-v1-original-byte-aliases.json';alia=read(aliap)
assert H(aliap)=='beaf3df1dc91bb8df50900ba1cc5e2efd1450a5a4935a815835f0a03133e7ea3' and alia['actual_exit_code']==1
assert len(alia['original_simulation_file_aliases'])==29
for row in alia['original_simulation_file_aliases'].values():assert H(ROOT/row['archive_file'])==row['sha256']
assert not (ROOT/'book/coverage/checks/root-source-batch52/prewrite-plan-v1.json').exists()
assert H(ROOT/'book/coverage/inventory.json')=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
report={'status':'passed_independent_source52_writer_v3_exact_assembly_delta_and_actual_three_proof_catalogue_fixture',
 'reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(NEW),'helper_sha256':H(NEW),
 'checker':ref(Path(__file__)),'previous_review':ref(priorp),'entire_original_v2_review_body_and_time':prior,
 'catalogue':ref(catalogp),'protect_and_all_other_dry_apply_code_AST_unchanged':True,
 'actual_pure_original_assembly_failure':old_failure,'actual_pure_corrected_three_proof_catalogue_page':expected,
 'original_item_body_unchanged':True,'preserved_genuine_root_failed_dry':{'record':ref(failp),'entire_original_record_body_and_time':fail,'raw_log':ref(ROOT/fail['log']),'simulation_alias_catalogue':ref(aliap),'archived_simulation_html_count':29},
 'errors':[],'writer_main_dry_apply_executed':False,
 'scope':'Narrow code delta plus genuine pure fixture of the exact actual catalogue item. Original v2 code review missed the inherited duplicate-key assembly; actual Root dry failed before plan/source/inventory mutation. Original helper/review/failure/history unchanged. Full protect is reused from the exact prior actual read-only pass, not rerun or retimed. Root actual corrected dry/apply are separate future executions.'}
with OUT.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'review':ref(OUT),'helper_sha256':H(NEW),'writer_main_executed':False}))
