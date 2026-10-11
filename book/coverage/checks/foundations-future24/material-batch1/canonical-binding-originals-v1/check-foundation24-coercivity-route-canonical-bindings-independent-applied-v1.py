from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');D=ROOT/'book/coverage/checks/foundations-future24/material-batch1'
def P(p):return Path(p) if Path(p).is_absolute() else ROOT/p
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
def read(p):return json.loads(P(p).read_text())
def ref(p):q=P(p);return {'file':str(q.relative_to(ROOT)) if q.is_relative_to(ROOT) else str(q),'sha256':H(q)}
allready=D/'five-source37-export-actual-canonical-readiness24-v1.json';assert H(allready)=='758e81e120ab257f9b87fe0c6602ce92bfab26d3f90ca6d4a726937ca293164d'
summary=read(allready);assert summary['source_count']==5 and summary['public_theorem_count']==37
inv=read('book/coverage/inventory-after-correction51.json');us={u['key']:u for u in inv['material_source_units']}
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
rows=[]
for lab,digest,peerhash,unitkey,count in [('coercivity1150','fccefdf6e8f8b7d08ac42b8149aec87dae9ccbcc68cae3934bbeed00b42a77e0','cd7a49b2d5fc94df86ed098a986c960c1514191db59604fcce053aab275bbb44','primer-basics.html::node-1150',7),('printed-route1158','d9fd47580c8edf9ffa06db8d81cbc8b0e9dfbf1c8175ea152d00a235f0aab776','00949ccf9ec0822634b0b09e905bc69208cf22eef5d8787739097ecc20a008f9','primer-basics.html::node-1158',8)]:
 readiness=D/lab/'source-exact-canonical-paired-readiness24-v1.json';r=read(readiness);assert ref(readiness) in summary['groups']
 src=r['canonical_source'];assert src['sha256']==digest==H(src['file'])==H(r['canonical_source_snapshot']['file'])
 peerref=r['original_full_semantic_peer'];assert H(peerref['file'])==peerref['sha256']==peerhash
 peer=read(peerref['file']);assert peer==r['entire_original_full_semantic_peer_body_and_time']
 orig=Path('/tmp')/Path(peerref['file']).name;assert orig.read_bytes()==P(peerref['file']).read_bytes()
 assert peer['status']=='independent_whole_literal_source_review_passed' and peer['reviewer']=='/root/applied_next'
 proof=next(s for s in peer['proof_sources'] if s['sha256']==digest);assert P(proof['file']).read_bytes()==P(src['file']).read_bytes()
 names=[d['name'] for d in declarations(P(src['file']).read_text()) if d['kind'] in ['theorem','lemma']]
 assert len(names)==count and names==r['public_theorem_names']
 requestref=r['original_TMP_request'];request=read(requestref['file']);assert H(requestref['file'])==requestref['sha256'] and request==r['entire_original_TMP_request_body_and_time']
 u=next(z for z in peer['material_units'] if z['source_unit_key']==unitkey)
 assert u['whole_unit_approved'] is True and u['material_status']=='proved' and u['missing_clauses']==[] and u['entire_inventory_record']==us[unitkey]
 records=[]
 for pair in r['actual_canonical_pair']:
  pref=pair['actual_record'];a=read(pref['file']);assert H(pref['file'])==pref['sha256']
  assert a['actual_exit_code']==0 and a['source']==src['file'] and a['source_unchanged'] and a['source_sha256_before']==a['source_sha256_after']==digest
  assert H(a['log'])==a['log_sha256']==pair['raw_log']['sha256'] and a['log']==pair['raw_log']['file']
  assert H(a['source_snapshot'])==a['source_snapshot_sha256']==digest==pair['source_snapshot']['sha256']
  assert a['actual_workdir']==str(ROOT/'verification/lean') and a['started_at_utc'] and a['finished_at_utc'] and a['elapsed_seconds']>=0
  assert a['actual_command']==(['lake','build','SafeLearning.'+P(src['file']).stem] if a['kind'].endswith('named-build') else ['lake','env','lean','SafeLearning/'+P(src['file']).name])
  assert H(a['actual_pair_helper'])==a['actual_pair_helper_sha256'];records.append({'record':pref,'raw_log':pair['raw_log'],'source_snapshot':pair['source_snapshot'],'actual_exit_code':0})
 assert len(records)==2
 for original,alias in r['all_original_TMP_byte_copies'].items():assert H(original)==H(alias['file'])==alias['sha256']
 rows.append({'group':lab,'canonical_readiness':ref(readiness),'canonical_source':src,'original_full_semantic_peer':peerref,'original_review_time':peer['reviewed_at_utc'],'entire_original_review_body':peer,'material_unit_exact_original_decision':u,'new_actual_canonical_pairs':records,'public_theorem_count':count,'all_original_TMP_history_byte_copies':r['all_original_TMP_byte_copies']})
manifest=read('reports/full-coverage/checkpoint-23-manifest.json');assert len(manifest['proof_files'])==1131
for n,d in manifest['proof_files'].items():assert H(n)==d['sha256'],n
held={n:d for n,d in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/') or n in ['book/coverage/inventory.json','book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
for n,d in held.items():assert H(n)==d,n
out=Path('/tmp/foundations24-coercivity-and-printed-route-canonical-binding-independent-applied-confirmation-v1.json');assert not out.exists()
out.write_text(json.dumps({'status':'passed_exact_canonical_source_and_actual_evidence_binding_original_whole_semantics_retained','reviewer':'/root/applied_next','checked_at_utc':datetime.now(timezone.utc).isoformat(),'batch_readiness':ref(allready),'groups':rows,'counts':{'new_sources_bound':2,'public_theorem_bodies_exact_originals':15,'genuine_new_canonical_zero_records':4,'whole_unit_decisions_retained':2,'protected_selected23_sources':1131},'actual_checker':str(Path(__file__)),'actual_checker_sha256':H(__file__),'held_current_owner_inventory_source_sha256':held,'scope':'Supplemental exact canonical-source/execution correspondence only. Both complete original full-literal mathematical decisions, hypotheses, bodies and review times remain unchanged. New named/standalone records are genuine actual0; no new semantic decision, current owner mutation, aggregate24 audit or coverage deployment inferred.','errors':[],'coverage_complete':False},indent=2,ensure_ascii=False)+'\n');print(out,H(out))
