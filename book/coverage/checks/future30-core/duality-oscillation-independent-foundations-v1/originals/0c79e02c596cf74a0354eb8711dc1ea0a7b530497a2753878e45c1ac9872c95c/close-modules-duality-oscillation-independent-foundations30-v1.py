from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=ROOT/'book/coverage/checks/future30-core/duality-oscillation-independent-foundations-v1'
FIND=Path('/tmp/modules-duality-oscillation-independent-foundations30-findings-v1.json');ACTUAL=Path('/tmp/modules-duality-oscillation-independent-foundations30-actual-v1.json');CONTEXT=Path('/tmp/root_tmp_lean_current65_owner29_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(q):
 p=Path(q['file']);return p if p.is_absolute()else ROOT/p
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(ROOT)),'sha256':sha(p),'bytes':p.stat().st_size}
ctx=json.loads(CONTEXT.read_bytes());protected={**ctx['pins_sha256'],**ctx['held_current_source_sha256'],**ctx['owners_sha256']};assert all(sha(ROOT/n)==h for n,h in protected.items())
d=json.loads(FIND.read_bytes());a=json.loads(ACTUAL.read_bytes());assert a['status']=='passed' and type(a['actual_exit_code'])is int and a['actual_exit_code']==0 and a['protection_errors']==[];assert a['helper_sha256_before']==a['helper_sha256_after'] and sha(a['log'])==a['log_sha256'];assert d['errors']==[] and d['narrow_wording_approved']is True
REQUEST=Path(d['request']['file']);proposal=json.loads(REQUEST.read_bytes())
closed={};aliases={}
def bind(p):
 p=Path(p);p=p if p.is_absolute()else ROOT/p;h=sha(p)
 # Existing immutable candidates/inventories are retained through their physical Root files.
 if p.is_relative_to(ROOT) and p.resolve().is_relative_to(ROOT) and ('inventory-after-correction65.json'==p.name or 'current65-pair-bound-v7' in str(p)):
  q=p
 else:
  q=BASE/'originals'/h/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==h
  else:
   with q.open('xb')as f:f.write(p.read_bytes())
 aliases[str(p)]=ref(q);closed[str(q.relative_to(ROOT))]=h;return ref(q)
for k in ['source','before_inventory','before_corrections','parser','validator','proposed_source','original_owner29_candidate','proposed_full29_inventory','actual_parser_stdout','actual_supporting_positive_budget_no_oscillation_countermodel_source','actual_supporting_passed_trial10','actual_supporting_source_snapshot','actual_supporting_raw_log']:
 p=path(proposal[k]);assert sha(p)==proposal[k]['sha256'];bind(p)
for p in [REQUEST,FIND,ACTUAL,Path(a['log']),CONTEXT,Path('/tmp/check-modules-duality-oscillation-independent-foundations30-v1.py'),Path('/tmp/run-modules-duality-oscillation-independent-foundations30-v1.py'),Path(d['fresh_full29_inventory']['file']),Path('/tmp/prepare-modules-duality-oscillation-unnumbered-proposal30-v1.py'),Path('/tmp/run-modules-duality-oscillation-unnumbered-proposal30-preparation-v1.py'),Path('/tmp/modules-duality-oscillation-unnumbered-proposal30-preparation-actual-v1.json'),Path('/tmp/modules-duality-oscillation-unnumbered-proposal30-preparation-actual-v1.log'),ROOT/'sources/text/pid_raw.txt',Path(__file__)]:bind(p)
parentnative=json.loads(Path('/tmp/modules-duality-oscillation-unnumbered-proposal30-preparation-actual-v1.json').read_bytes());assert type(parentnative['actual_exit_code'])is int and parentnative['actual_exit_code']==0 and parentnative['protection_errors']==[]
def norm(v):
 if isinstance(v,dict):
  z={k:norm(w)for k,w in v.items()}
  if 'file'in v and 'sha256'in v:
   p=path(v);assert sha(p)==v['sha256'];assert str(p)in aliases;z.update(aliases[str(p)])
  return z
 if isinstance(v,list):return [norm(w)for w in v]
 return v
peer=norm(d)
peer.update(reviewer='/root/foundations_recovery28',closed_at_utc=datetime.now(timezone.utc).isoformat(),original_full_findings=bind(FIND),original_review_finished_at_utc=d['finished_at_utc'],actual_reader=bind(ACTUAL),actual_raw_log=bind(a['log']),reader_helper=bind('/tmp/check-modules-duality-oscillation-independent-foundations30-v1.py'),reader_wrapper=bind('/tmp/run-modules-duality-oscillation-independent-foundations30-v1.py'),actual_author_parser_preparation=bind('/tmp/modules-duality-oscillation-unnumbered-proposal30-preparation-actual-v1.json'),current_source_original=norm(proposal['source']),proposed_source_original=norm(proposal['proposed_source']),actual_supporting_passed_trial10=norm(proposal['actual_supporting_passed_trial10']),all_original_body_and_time_preserved=True,all_original_byte_aliases=aliases,required_evidence_artifacts_sha256=closed,actual_protected_original_context=bind(CONTEXT),actual1197_31_five_before_after_unchanged=True,prospective_postfreeze_evidence_not_part_of_frozen29=True)
out=BASE/'modules-duality-can-oscillate-unnumbered-narrow-literal-parser-independent-foundations30-closed-peer-v1.json';assert not out.exists();out.write_text(json.dumps(peer,ensure_ascii=False,indent=2)+'\n');assert all(not(ROOT/n).is_symlink()and(ROOT/n).resolve().is_relative_to(ROOT)and sha(ROOT/n)==h for n,h in closed.items());assert all(sha(ROOT/n)==h for n,h in protected.items());print(json.dumps({'peer':ref(out),'physical_refs':len(closed),'original_aliases':len(aliases),'actual_reader_code':0,'protection_errors':[]}))
