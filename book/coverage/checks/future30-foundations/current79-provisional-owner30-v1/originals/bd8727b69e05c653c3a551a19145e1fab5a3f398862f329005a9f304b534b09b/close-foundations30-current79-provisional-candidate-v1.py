from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy
R=Path('/home/oxrexkevin/SafetyBased');BASE=R/'book/coverage/checks/future30-foundations/current79-provisional-owner30-v1';assert not BASE.exists()
OLD=Path('/tmp/foundations30-current79-provisional-candidate-v3/foundations30-current79-provisional-offer-v3.json');ACT=Path('/tmp/foundations30-current79-provisional-candidate-preparation-actual-v3.json');CTX=Path('/tmp/root_tmp_lean_current79_historical_owner29_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(R).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
def path(n):
 p=Path(n);return p if p.is_absolute() else R/p
assert sha(OLD)=='487db9605472bae99a43526f10ad09e2e48bf56308f79128c13213a47cb27d8c'
d=json.loads(OLD.read_bytes());a=json.loads(ACT.read_bytes());c=json.loads(CTX.read_bytes());protected={**c['pins_sha256'],**c['held_current_source_sha256'],**c['owners_sha256']};assert all(sha(R/n)==h for n,h in protected.items())
assert a['status']=='passed' and a['actual_exit_code']==0 and a['protection_errors']==[] and a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['log'])==a['log_sha256']
assert d['errors']==[] and d['all_new_actual_canonical_pairs_pending'] is True and (d['new_proof_file_count'],d['new_theorem_or_lemma_count'],d['new_whole_material_unit_count'])==(27,370,58)
closed={};aliases={}
immutable={'book/coverage/foundations.json':R/'reports/full-coverage/checkpoint-29/book/coverage/foundations.json','book/coverage/inventory.json':R/'book/coverage/inventory-after-correction79.json'}
def bind(n):
 p=path(n);h=sha(p);rel=p.relative_to(R).as_posix() if p.is_relative_to(R) else None
 if rel in immutable:
  q=immutable[rel];assert sha(q)==h
 elif p.is_relative_to(R) and not p.is_symlink() and p.resolve().is_relative_to(R):q=p
 else:
  q=BASE/'originals'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==h
  else:
   with q.open('xb') as f:f.write(p.read_bytes())
 r=ref(q);aliases[str(p)]=r
 if rel:aliases[rel]=r
 closed[r['file']]=h;return r
for n,h in d['required_evidence_artifacts_sha256'].items():assert sha(path(n))==h;bind(n)
for p in [OLD,ACT,Path(a['log']),CTX,Path('/tmp/prepare-foundations30-current79-provisional-candidate-v3.py'),Path('/tmp/run-foundations30-current79-provisional-candidate-preparation-v3.py'),Path(__file__)]:bind(p)
cr=bind(d['candidate']['file']);ir=bind(d['exact_interface']['file']);offer=copy.deepcopy(d)
for dest,row in offer['proof_files'].items():
 for field in ['original_exact_source','original_genuine_TMP_final_native','original_genuine_TMP_source_snapshot','original_genuine_TMP_raw_log','independent_full_source_correspondence_peer']:
  q=row[field];assert sha(path(q['file']))==q['sha256'];row[field]=bind(q['file'])
 row['evidence_sha256']={bind(n)['file']:h for n,h in row['evidence_sha256'].items()}
offer.update(status='closed_current79_Foundation_owner30_provisional_offer_pending_genuine_canonical_pairs_and_full_mapping',closed_at_utc=datetime.now(timezone.utc).isoformat(),candidate=cr,mapped_ledger=cr['file'],mapped_ledger_sha256=cr['sha256'],exact_interface=ir,original_exact_author_provisional_offer=bind(OLD),actual_author_preparation=bind(ACT),actual_author_preparation_raw=bind(a['log']),original_preparation_helper=bind('/tmp/prepare-foundations30-current79-provisional-candidate-v3.py'),original_preparation_wrapper=bind('/tmp/run-foundations30-current79-provisional-candidate-preparation-v3.py'),actual79_context=bind(CTX),original_installed29_ledger=bind(R/'book/coverage/foundations.json'),inventory=bind(R/'book/coverage/inventory.json'),approved_scope_plan=bind(d['approved_scope_plan']['file']),actual_Source66_to79_application=bind(d['actual_Source66_to79_application']['file']),actual_Source66_to79_native=bind(d['actual_Source66_to79_native']['file']),original_internal_candidate_and_interface_refs_preserved_as_exact_byte_aliases=True,original_closed_byte_aliases=aliases,required_evidence_artifacts_sha256=closed,additional_frozen_inputs=closed,protection_errors=[],current_Source79_and_1197_31_raw5_unchanged=True,canonical_pairs_executed_by_author=False)
p=BASE/'foundations30-current79-provisional-owner30-root-offer-v1.json';p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(offer,ensure_ascii=False,indent=2)+'\n')
assert all(not (R/n).is_symlink() and (R/n).resolve().is_relative_to(R) and sha(R/n)==h for n,h in closed.items());assert all(sha(R/n)==h for n,h in protected.items())
print(json.dumps({'offer':ref(p),'candidate':cr,'exact_interface':ir,'physical_refs':len(closed),'aliases':len(aliases),'sources_public_bodies':[27,370],'whole_keys_rows':[58,63],'nonformal_rows':3,'component_rows':4,'counts':d['material_claim_counts'],'pending_physical':354,'actual_author_seconds':a['elapsed_seconds'],'actual_pairs_pending':True,'errors':[]}))
