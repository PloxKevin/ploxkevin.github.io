from pathlib import Path
import json,hashlib
from datetime import datetime,timezone
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
rp=Path('/tmp/root-core26-box-label-literal-source-review-request-v1.json');dp=Path('/tmp/core26-box-label-118-manual-decisions-v1.json')
assert sha(rp)=='9f7596d303dc2d6ce559061d2c0225b8be62342ad33954a3388b5cbe8ba140e8'
r=read(rp);decisions=read(dp)
assert len(r['whole_units'])==len(decisions)==118
invp=ROOT/'book/coverage/inventory.json';cp=ROOT/'book/coverage/core.json'
assert sha(invp)==r['inventory_sha256']=='38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'
assert sha(cp)==r['original_core24_sha256']=='47b676890af40692cc1161c5472b461397b224e1a3724ee6990f03bb64d56bf5'
inv=read(invp);core=read(cp);units={u['key']:u for u in inv['material_source_units']};claims={u['id']:u for u in core['material_claims']}
protected_names=['book/coverage/'+n for n in ['core.json','modules.json','foundations.json','applied.json','applied-promotions.json','inventory.json']]
protected={n:sha(ROOT/n) for n in protected_names}
source_hashes={};seen=set();counts={'nonformal':0,'pending':0}
for i,(u,d) in enumerate(zip(r['whole_units'],decisions)):
 old=u['entire_original_pending_claim_body_and_time'];rec=u['entire_inventory_record'];ctx=u['full_literal_context']
 assert rec==units[rec['key']] and rec['key'] not in seen;seen.add(rec['key'])
 assert old==claims[old['id']] and old['status']=='pending'
 assert d['request_index']==i and d['source_unit_key']==rec['key']
 for k in ['entire_inventory_record','entire_original_pending_claim_body_and_time','full_literal_context']:assert d[k]==u[k]
 assert d['material_status'] in counts and d['lean_declarations']==d['hypotheses']==[]
 assert d['whole_unit_approved'] is (d['material_status']=='nonformal')
 assert bool(d['missing_clauses']) is (d['material_status']=='pending')
 assert isinstance(d['per_unit_reason'],str) and len(d['per_unit_reason'])>50
 assert hashlib.sha256(rec['source_text'].encode()).hexdigest()==rec['text_sha256']
 source=ROOT/rec['source'];source_hashes[rec['source']]=sha(source)
 assert source_hashes[rec['source']]==rec['source_sha256']==inv['source_sha256'][rec['source']]
 assert ctx['source']==rec['source']
 assert '\n'.join(source.read_text().splitlines()[ctx['start_line']-1:ctx['end_line']])==ctx['raw_html']
 counts[d['material_status']]+=1
assert counts=={'nonformal':48,'pending':70}
# Six concrete pages plus the glossary account for every exact context; no class-based inference was used.
assert len(source_hashes)==6
manifest=read(ROOT/'reports/full-coverage/checkpoint-24-manifest.json')
assert len(manifest['proof_files'])==1144 and len(manifest['frozen_inputs_sha256'])==40485
for n,row in manifest['proof_files'].items():assert sha(ROOT/n)==row['sha256'],n
snapshot=ROOT/manifest['snapshot']
for n,digest in manifest['frozen_inputs_sha256'].items():assert sha(snapshot/n)==digest,n
assets={n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')}
assert len(assets)==31
for n,h in assets.items():assert sha(ROOT/n)==h,n
for n,h in protected.items():assert sha(ROOT/n)==h,n
out={'status':'passed_read_only_exact_118_individual_label_review_identity_and_protection_checks','errors':[],'checked_at_utc':datetime.now(timezone.utc).isoformat(),'request_sha256':sha(rp),'manual_decisions_sha256':sha(dp),'counts':counts,'full_context_pages_sha256':source_hashes,'unchanged_live_owner_inventory_sha256':protected,'selected24_sources_rehashed':1144,'frozen24_inputs_rehashed':40485,'current52_assets_rehashed':31,'scope':'Checker validates explicit individual human-level semantic decisions and exact supplied contexts. No classifier-by-tag, compiler, aggregate, live mapping or source write.'}
p=Path('/tmp/core26-box-label-118-independent-applied-check-findings-v1.json')
with p.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'counts':counts,'proofs':1144,'frozen_inputs':40485}))
