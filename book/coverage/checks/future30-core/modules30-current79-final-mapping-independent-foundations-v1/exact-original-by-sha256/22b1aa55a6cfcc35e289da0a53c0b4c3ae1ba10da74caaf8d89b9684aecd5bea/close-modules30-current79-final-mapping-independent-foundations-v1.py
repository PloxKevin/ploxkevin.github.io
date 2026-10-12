from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future30-core/modules30-current79-final-mapping-independent-foundations-v1';F=Path('/tmp/modules30-current79-real30-independent-foundations-findings-v4.json');N=Path('/tmp/modules30-current79-real30-independent-foundations-actual-v4.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R)),'sha256':sha(p),'bytes':p.stat().st_size}
assert not B.exists();d=json.loads(F.read_bytes());a=json.loads(N.read_bytes());assert a['status']=='passed' and a['actual_exit_code']==0 and a['protection_errors']==[] and a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['log'])==a['log_sha256'];assert d['errors']==[]
assert a['actual_command']==['python3','/tmp/review-modules30-current79-real30-independent-foundations-v4.py'] and a['actual_workdir']==str(R)
protected=a['protected_inputs_sha256_before'];assert sum(n.startswith('verification/lean/SafeLearning/') for n in protected)==1242
assert all(sha(R/n)==h for n,h in protected.items())
closed={};aliases=dict(d['original_closed_byte_aliases']);mutableowners={R/'book/coverage'/f'{n}.json' for n in ['core','foundations','applied','modules','applied-promotions']}
def bind(p):
 p=Path(p);p=p if p.is_absolute() else R/p;h=sha(p);assert p not in mutableowners
 if p.is_relative_to(R) and p.resolve().is_relative_to(R) and not p.is_symlink():q=p
 else:
  q=B/'exact-original-by-sha256'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==h
  else:
   with q.open('xb') as f:f.write(p.read_bytes())
 r=ref(q);aliases[str(p)]=r;closed[r['file']]=h;return r
for n,h in d['required_evidence_artifacts_sha256'].items():assert sha(n)==h;bind(n)
for p in [F,N,Path(a['log']),Path(__file__),Path('/tmp/run-review-modules30-current79-real30-independent-foundations-v4.py')]:bind(p)
actualaliases={n:bind(n) for n in [*a['helper_sha256_before'],a['log']]}
peer={k:v for k,v in d.items() if k not in ['required_evidence_artifacts_sha256','original_closed_byte_aliases']}
peer.update({'status':'passed_independent_modules30_current79_real15_source30_pair_three_fragment_full_scope_mechanics_mapping_review','closed_at_utc':datetime.now(timezone.utc).isoformat(),'full_mapping_read':True,'all_three_inverse_stages_entire_raw29_dictionary_and_byte_exact':True,'all_math_status_names_native_pair_original_body_times_and_counts_unchanged_by_three_fragment_overlay':True,'original_full_mapping_findings':bind(F),'actual_finalizer':bind(N),'actual_finalizer_original_byte_aliases':actualaliases,'actual_independent_reader_raw':bind(a['log']),'reader_helper':bind('/tmp/review-modules30-current79-real30-independent-foundations-v4.py'),'reader_wrapper':bind('/tmp/run-review-modules30-current79-real30-independent-foundations-v4.py'),'protected_actual_canonical_proof_source_count':1242,'unchanged_current79_book_asset_count':31,'unchanged_historical29_raw_owners':5,'actual1242_31_five_and_current_chapter_fragments_before_after_unchanged':True,'location_first_warning_header_metadata_is_preserved_original_not_zero_all_named_replay_warnings_claim':True,'required_evidence_artifacts_sha256':closed,'original_closed_byte_aliases':aliases,'protection_errors':[]})
p=B/'modules30-current79-real30-three-fragment-full-mapping-independent-foundations30-closed-peer-v1.json';assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(peer,ensure_ascii=False,indent=2)+'\n')
assert all(not (R/n).is_symlink() and (R/n).resolve().is_relative_to(R) and sha(R/n)==h for n,h in closed.items());assert all(sha(R/n)==h for n,h in protected.items())
print(json.dumps({'peer':ref(p),'physical_refs':len(closed),'aliases':len(aliases),'actual_reader_exit_code':a['actual_exit_code'],'actual_reader_seconds':a['elapsed_seconds'],'counts':d['counts'],'sources_public_pairs':[15,504,30],'whole_exercises_units':[8,32],'coverage_complete':False,'errors':[]}))
