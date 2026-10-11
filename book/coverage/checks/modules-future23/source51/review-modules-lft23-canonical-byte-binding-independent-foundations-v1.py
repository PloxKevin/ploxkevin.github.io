from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,traceback,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp');START=datetime.now(timezone.utc).isoformat()
READY=ROOT/'book/coverage/checks/modules-future23/source51/lft/lft-source51-input-bindings-v1.json';OUT=TMP/'modules-lft23-canonical-source-original-full-peer-independent-foundations-binding-v1.json';FAIL=TMP/'modules-lft23-canonical-independent-foundations-binding-failure-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):return {'file':str(p),'sha256':sha(p)}
def check(r):
 p=path(r.get('file',r.get('path')));assert sha(p)==r['sha256'] and not p.is_symlink(),r;return p
def write(p,d):
 with p.open('x') as f:f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def main():
 assert not OUT.exists() and not FAIL.exists() and sha(READY)=='ef9aa484215f8d5358de7968a851ba79d857b69157b7cd33cf6cbf7077c42c83'
 q=read(READY);peerpath=check(q['original_review']);assert sha(peerpath)=='54e1f8c16c4228601bc1e2afd711ddb69abbcbbc51ea66bdd891ff1060a2b10c';peer=read(peerpath);assert peer==q['entire_original_review_body_and_time'] and 'passed' in peer['status'] and peer['errors']==[]
 invpath=ROOT/q['inventory'];assert sha(invpath)==q['inventory_sha256']==sha(ROOT/'book/coverage/inventory.json')=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41';inv=read(invpath)
 assert peer['entire_original_exercise_record']==next(r for r in inv['exercises'] if r['key']==q['whole_exercise_key'])
 units={r['key']:r for r in inv['material_source_units']}
 assert all(r['entire_inventory_record']==units[r['source_unit_key']] for r in peer['material_units']) and len(peer['material_units'])==6
 aliases=read(check(q['canonical_path_aliases']))['aliases']
 for original,r in aliases.items():assert path(original).read_bytes()==check(r).read_bytes() and r['original_path']==original
 body_by_digest={r['source']['sha256']:r for r in peer['full_source_reviews']};records=[];bodies=[];names=set()
 for p in q['proof_files']:
  source=ROOT/p['source'];assert sha(source)==p['sha256'];original=body_by_digest[p['sha256']];text=source.read_text();assert text==original.get('entire_source_and_all13_bodies',original.get('entire_source_and_all3_bodies'))
  ns=re.search(r'^namespace ([A-Za-z0-9_.]+)$',text,re.M).group(1);public=[ns+'.'+n for n in re.findall(r'^theorem\s+(\w+)',text,re.M)];assert public==p['public_declarations']==original['public_declarations'];names.update(public);bodies.append({'canonical_source':ref(source),'original_entire_full_source_review':original})
  for i,actual in enumerate(p['actual_paired_records']):
   r=read(check(actual['actual_record']));snapshot=check(actual['source_snapshot']);log=check(actual['raw_log'])
   assert r['actual_exit_code']==actual['actual_exit_code']==0 and r['source_unchanged'] is True
   assert r['source_sha256_before']==r['source_sha256_after']==p['sha256']==sha(snapshot) and snapshot.read_bytes()==source.read_bytes()
   assert r['command']==(['lake','env','lean',f'SafeLearning/{source.name}'] if i==0 else ['lake','build',f'SafeLearning.{source.stem}']) and r['actual_workdir']==str(ROOT/'verification/lean')
   assert sha(log)==r['log_sha256'] and not re.search(r'\berror(?:\(|:)',log.read_text())
   records.append({'actual_record':actual['actual_record'],'entire_original_actual_record':r,'raw_log':actual['raw_log'],'source_snapshot':actual['source_snapshot']})
 assert len(names)==16 and len(records)==4 and q['counts']=={'new_whole_exercises':1,'material_units':6,'new_sources':2,'public_theorem_exports':16,'genuine_actual_paired_records':4}
 prep=TMP/'modules-lft23-source51-input-preparation-actual-v1.json';prepbody=read(prep);assert prepbody['actual_exit_code']==0
 manifest=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json');assert len(manifest['proof_files'])==1113
 for n,r in manifest['proof_files'].items():assert sha(ROOT/n)==r['sha256']
 for n,h in peer['held22_ledgers_sha256'].items():assert sha(ROOT/n)==h
 result={'status':'passed_exact_two_canonical_lft_sources_four_actual_records_original_full_semantic_body_time_binding','reviewer':'/root/config21_next','checked_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'errors':[],'canonical_readiness':ref(READY),'original_complete_literal_peer':q['original_review'],'entire_original_complete_literal_peer_body_and_time':peer,'original_reviewed_at_utc_unchanged':peer['reviewed_at_utc'],'actual_archive_preparation':ref(prep),'all_canonical_aliases_equal_original_TMP_bytes':True,'original_artifact_alias_count':len(aliases),'canonical_sources_equal_entire_original_full_source_reviews':bodies,'all_four_genuine_canonical_records_raw_logs_snapshots_exact':records,'whole_exercise_and_six_original_decisions_reason_hypotheses_names_time_unchanged':True,'current_inventory':ref(invpath),'all1113_selected22_sources_four_held22_ledgers_exact':True,'semantic_redecision':False,'limits':['Only exact canonical source/pair/history binding supplements the original full16-body/six-literal decision. The original decision and review time remain unchanged.','Both new sources now have genuine canonical standalone and named target0 records. This report does not execute Lean, install an owner candidate, select proofs, assert global23 or publication.']}
 write(OUT,result);print(json.dumps({'status':result['status'],'review':ref(OUT),'sources':2,'actual_records':4,'original_aliases':len(aliases)}))
if __name__=='__main__':
 try:main()
 except Exception:
  msg=traceback.format_exc()
  if not FAIL.exists():write(FAIL,{'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_checker':ref(Path(__file__)),'failure':msg})
  sys.stderr.write(msg);sys.exit(1)
