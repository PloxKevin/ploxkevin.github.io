from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=Path('/tmp/root-core25-case-study-guidance-five-whole-units-review-request-v1.json')
REQUEST_SHA='3a404d0d745a4b13c0b58142303a177e24cc43375a146dab657456231a47dce3'
OUT=Path('/tmp/root-core25-case-study-guidance-five-whole-units-independent-applied-review-v1.json')
assert not OUT.exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(REQUEST)==REQUEST_SHA
request=json.loads(REQUEST.read_text())
inventory_name='book/coverage/inventory-after-correction52.json'
assert sha(ROOT/inventory_name)==sha(ROOT/'book/coverage/inventory.json')==request['inventory_sha256']
inventory=json.loads((ROOT/inventory_name).read_text())
units={r['key']:r for r in inventory['material_source_units']}
source=request['source'];assert sha(ROOT/source)==request['source_sha256']
lines=(ROOT/source).read_text().splitlines()
core=json.loads((ROOT/'book/coverage/core.json').read_text());claims={r['id']:r for r in core['material_claims']}
reasons={
 'case-studies.html::node-15':'The complete subtitle describes the three connected teaching cases and the format of their worked routes, assumptions, transfer exercises and checks. Reading the page confirms these case headings; the subtitle supplies no state bound, probability, algorithmic guarantee or mathematical conclusion.',
 'case-studies.html::node-18':'The complete paragraph instructs the learner to attempt each model and identify observations, choices, uncertainty and the meaning of safety. Its teaching-data provenance and warning that conclusions depend on displayed assumptions are methodological scope statements. It asserts no new quantitative law or correctness of every neighboring worked calculation.',
 'case-studies.html::node-43':'Every sentence documents the scope of the displayed discrete tank certificate. Policy efficiency and physical validity of constructed bounds are outside its evidence; sampled-state induction supplies no intervening-time model; stuck actuators, delay and larger inflows are excluded assumptions. These are limitations of that argument and instructions for reporting them, not an independent universal impossibility theorem or a guarantee for the neighboring numerical cases.',
 'case-studies.html::node-164':'The full paragraph gives report-writing guidance: distinguish a mathematical model argument, a numerical candidate and application-assumption evidence. The quoted examples name types of claims rather than assert any particular theorem. Its final sentence directs readers to contents and glossary; it contains no model, numerical premise or mathematical implication to certify.',
 'case-studies.html::node-167':'The entire navigation container consists of the Book contents and Begin at Chapter0 link labels. Their actual destinations are navigation to book.html and primer-basics.html; neither label states a mathematical proposition or an execution guarantee.'}
records=[]
assert len(request['whole_units'])==len(reasons)==5
for row in request['whole_units']:
 unit=row['inventory_unit'];key=unit['key'];assert unit==units[key]
 assert row['entire_pending_claim']==claims[row['entire_pending_claim']['id']]
 assert unit['source_sha256']==request['source_sha256']
 ctx=row['full_local_context'];assert ctx['raw_html']=='\n'.join(lines[ctx['start_line']-1:ctx['end_line']])
 records.append({'source_unit_key':key,'entire_inventory_record':unit,
  'entire_original_pending_claim_body_and_time':row['entire_pending_claim'],
  'material_status':'not_a_formal_claim','review_status':'not_a_formal_claim','whole_unit_approved':True,
  'lean_declarations':[],'hypotheses':[],'missing_clauses':[],
  'per_unit_reason':reasons[key],'full_literal_context':ctx,
  'scope':'Whole classification of this exact unit only. Neighboring mathematical models, computations, certificates and exercise answers retain their own proof requirements.'})
assert 'href="book.html"' in lines[50] and 'href="primer-basics.html"' in lines[50]
for heading in ['id="case-tank"','id="case-tuning"','id="case-score"']:assert heading in '\n'.join(lines)
manifest=json.loads((ROOT/'reports/full-coverage/checkpoint-23-manifest.json').read_text())
assert len(manifest['proof_files'])==1131
for name,row in manifest['proof_files'].items():assert sha(ROOT/name)==row['sha256']
assert sha(ROOT/source)==request['source_sha256']
assert sha(ROOT/inventory_name)==sha(ROOT/'book/coverage/inventory.json')==request['inventory_sha256']
out={'status':'independent_full_five_case_study_guidance_literal_source_review_passed','errors':[],
 'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next',
 'request':{'file':str(REQUEST),'sha256':REQUEST_SHA},
 'inventory':{'file':inventory_name,'sha256':request['inventory_sha256']},
 'source':{'file':source,'sha256':request['source_sha256']},
 'material_units':records,'counts':{'whole_not_a_formal_claim':5,'new_proof_sources':0,'new_lean_declarations':0},
 'entire_request_body_and_time':request,'all1131_selected23_proof_hashes_exact':True,
 'scope':'Actual independent full literal/context reading and exact identity checker. All five units are separately approved as nonformal subtitle/instruction/proof-scope/report-guidance/navigation. All substantive neighboring mathematical statements remain excluded. No Lean run, full parent section/exercise proof, current24 mapping, HTML change or publication claim.',
 'coverage_complete':False}
OUT.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'review':str(OUT),'sha256':sha(OUT),'whole_nonformal_units':5}))
