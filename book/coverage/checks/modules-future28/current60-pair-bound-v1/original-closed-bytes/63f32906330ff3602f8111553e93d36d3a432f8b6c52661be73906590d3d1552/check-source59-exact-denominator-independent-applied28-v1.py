from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as F
import copy,hashlib,importlib.util,json,sys,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased');REQUEST=Path('/tmp/modules-physical-sensor-source59-proposal28-v2/modules-physical-sensor-source59-proposal28-v2.json');OUT=Path('/tmp/modules-source59-exact-denominator-independent-applied-findings28-v1.json');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(REQUEST)=='39eae6e09e69a9e9fd5b7165dced786137445336213cf90b5880eceeea8acfd3'
d=json.loads(REQUEST.read_bytes());closed={str(REQUEST):sha(REQUEST)}
def refs(x):
 if isinstance(x,dict):
  if type(x.get('file'))is str and type(x.get('sha256'))is str:
   p=Path(x['file']);assert p.is_file() and sha(p)==x['sha256'],str(p)
   if 'bytes' in x:assert p.stat().st_size==x['bytes']
   closed[str(p)]=sha(p)
  for v in x.values():refs(v)
 elif isinstance(x,list):
  for v in x:refs(v)
refs(d)
source=Path(d['source']['file']);before=source.read_text();old=d['before_raw_fragment'];new=d['after_raw_fragment'];proposed=Path(d['proposed_source']['file']).read_bytes();inv=json.loads(Path(d['before_inventory']['file']).read_bytes())
assert old==r'0.06/0.065320\approx0.918559' and new==r'0.06/(2\sqrt{4/3}\sqrt2(0.02))\approx0.918559'
assert before.count(old)==1 and new not in before and proposed==before.replace(old,new,1).encode() and proposed.decode().replace(new,old,1).encode()==source.read_bytes()
assert ''.join(before.splitlines(keepends=True)[795:802])==d['full_current_context_lines796_to802']
assert ''.join(proposed.decode().splitlines(keepends=True)[795:802])==d['full_proposed_context_lines796_to802']
# Positive square-root algebra: denominator=2 sqrt(4/3) sqrt2/50 has square8/1875;
# (3 sqrt6/8)^2=27/32; product equals(3/50)^2, so this is the exact positive quotient.
den_sq=F(8,1875);threshold_sq=F(27,32);assert den_sq*threshold_sq==F(3,50)**2
assert F(653195,10**7)**2 < den_sq < F(653205,10**7)**2
assert F(9185585,10**7)**2 < threshold_sq < F(9185595,10**7)**2
rounded_quotient=F(6,100)/F(65320,10**6)
assert F(9185545,10**7)<rounded_quotient<F(9185555,10**7)
assert den_sq>F(3,50)**2 and threshold_sq<F(1)
# Fresh independent full29 parser: BOTH globals isolated before first inventory call.
parser=Path(d['parser']['file']);sys.path.insert(0,str(ROOT/'book'))
with tempfile.TemporaryDirectory(prefix='applied-source59-independent-full29-') as td:
 isolate=Path(td);(isolate/'SafeLearning').mkdir()
 pages=sorted((ROOT/'SafeLearning').glob('*.html'));assert len(pages)==29
 for p in pages:(isolate/'SafeLearning'/p.name).write_bytes(proposed if p==source else p.read_bytes())
 spec=importlib.util.spec_from_file_location('source59_independent_applied_parser_v1',parser);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 m.ROOT=isolate;m.OUT=isolate/'book/coverage';assert m.ROOT!=ROOT and m.OUT!=ROOT/'book/coverage' and m.OUT.is_relative_to(m.ROOT)
 m.inventory();fresh=json.loads((m.OUT/'inventory.json').read_bytes())
assert fresh['counts']==inv['counts'] and len(fresh['source_sha256'])==29
assert fresh['source_sha256']=={**inv['source_sha256'],d['entire_changed_records']['lipsdp.html::node-998']['entire_proposed_inventory_record']['source']:sha(Path(d['proposed_source']['file']))}
changes={};changed={}
for field in ['exercises','material_source_units']:
 aa={r['key']:r for r in inv[field]};bb={r['key']:r for r in fresh[field]};assert aa.keys()==bb.keys();changes[field]=[]
 for k in aa:
  a=copy.deepcopy(aa[k]);b=copy.deepcopy(bb[k])
  if a['source']=='SafeLearning/lipsdp.html':
   assert b['source_sha256']==sha(Path(d['proposed_source']['file']));a.pop('source_sha256');b.pop('source_sha256')
  if a!=b:
   assert {n:v for n,v in a.items() if n not in ['source_text','text_sha256']}=={n:v for n,v in b.items() if n not in ['source_text','text_sha256']}
   changes[field].append(k);changed[k]={'entire_original_inventory_record':aa[k],'entire_proposed_inventory_record':bb[k]}
assert changes==d['fresh_parser_changed_text_keys']=={'exercises':['lipsdp.html#book-m12-b1'],'material_source_units':['lipsdp.html::node-998']}
assert changed==d['entire_changed_records']
provided=json.loads(Path(d['proposed_full29_inventory']['file']).read_bytes());assert {k:v for k,v in fresh.items() if k!='generated_at_utc'}=={k:v for k,v in provided.items() if k!='generated_at_utc'}
owner=json.loads(Path(d['current_modules_owner']['file']).read_bytes());assert next(x for x in owner['exercises'] if x['inventory_key']=='lipsdp.html#book-m12-b1')==d['entire_original_exercise_owner_row']
result={'status':'passed_independent_source59_exact_denominator_wording_and_isolated_full29_parser','errors':[],'reviewer':'Applied independent source and exact arithmetic reviewer','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'proposal':{'file':str(REQUEST),'sha256':sha(REQUEST)},'full_current_and_proposed_exercise_context_read':True,'exact_forward_and_inverse_entire_source_bytes':True,'both_parser_ROOT_and_OUT_isolated':True,'fresh_parser_literal_changes':changes,'all556_exercises_and12774_material_record_shapes_preserved':True,'entire_changed_records':changed,'entire_original_owner_exercise':d['entire_original_exercise_owner_row'],'arithmetic_decision':{'approved':True,'exact_denominator':'2 sqrt(4/3) sqrt2 (1/50)','exact_positive_threshold':'3 sqrt6/8','denominator_square':'8/1875','threshold_square':'27/32','exact_squared_identity':'(8/1875)*(27/32)=(3/50)^2','original_rounded_quotient_six_decimal':'0.918555','correct_exact_quotient_six_decimal':'0.918559','proof_of_rounding':'Strict rational squared bounds around the positive threshold establish rounding; no floating-point approximation is used as proof.'},'wording_decision':{'approved':True,'scope':'Only the erroneous use of rounded0.065320 as exact divisor is replaced by the actual SDP certificate expression. The exact box non-strict0.06 result and physical normalization clauses retain their entire literal text. No new whole-exercise or other material promotion follows from this source patch.'},'original_preparation_failure':d['original_failed_preparation_reference'],'closed_evidence_sha256':closed,'current_source_or_owner_or_selected_proofs_modified':False,'whole_mathematical_packet_approved':False,'scope':'Independent narrow complete source replacement/context, positive exact arithmetic and fresh fully isolated full29 parser review. Source59 remains prospective and only Root may apply it after checkpoint27 delivery.'}
with OUT.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'findings':str(OUT),'sha256':sha(OUT),'changed':changes}))
