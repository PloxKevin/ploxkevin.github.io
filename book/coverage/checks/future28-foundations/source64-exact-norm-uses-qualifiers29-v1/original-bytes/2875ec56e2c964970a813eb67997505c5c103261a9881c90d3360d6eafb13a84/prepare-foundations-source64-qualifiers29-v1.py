import hashlib,importlib.util,json,sys,tempfile
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/foundations-norm-uses-source64-proposal29-v1');OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def guard():
 ctx=json.loads(Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json').read_text())
 for name in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in ctx[name].items():assert sha(ROOT/n)==h,n
 return {'context_sha256':sha('/tmp/root_tmp_lean_current60_owner28_context_v1.json'),'selected_proofs':1186,'book_assets':31,'owners':5,'inventory_sha256':sha(ROOT/'book/coverage/inventory.json'),'corrections_sha256':sha(ROOT/'book/coverage/material-corrections.json')}
started=datetime.now(timezone.utc).isoformat();before=guard();src=ROOT/'SafeLearning/primer-linalg.html';raw=src.read_text()
replacements=[
 {'before':r'and $\max_{\|u\|\le u_{\max}}b^\top u=u_{\max}\|b\|$.','after':r'and, for $u_{\max}\ge0$, $\max_{\|u\|\le u_{\max}}b^\top u=u_{\max}\|b\|$.'},
 {'before':'A logit difference is','after':r'For a distinct class $j\ne y$, a logit difference is'},
 {'before':'And modules switch norms (Module 11 states its Lipschitz constants in the 1-norm): always check which norm a constant refers to.','after':r"And modules switch norms: Module 11's Berkenkamp bounds use the 1-norm, while its robust MPC uses Euclidean state norms and the input $\ell_\infty$ norm. Always check which norm a constant refers to."}]
new=raw
for q in replacements:assert new.count(q['before'])==1;new=new.replace(q['before'],q['after'])
rev=new
for q in reversed(replacements):assert rev.count(q['after'])==1;rev=rev.replace(q['after'],q['before'])
assert rev==raw and new.count('\n')==raw.count('\n')
candidate=OUT/'primer-linalg-proposed-source64.html';candidate.write_text(new)
sys.path.insert(0,str(ROOT/'book'));from validate import Document
assert [(n.tag,n.attrs,n.line) for n in Document(raw).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
iso=OUT/'isolated-full29-parser';(iso/'SafeLearning').mkdir(parents=True)
for p in (ROOT/'SafeLearning').glob('*.html'):(iso/'SafeLearning'/p.name).write_text(new if p==src else p.read_text())
assert len(list((iso/'SafeLearning').glob('*.html')))==29
sp=importlib.util.spec_from_file_location('source64_author_isolated_inventory',ROOT/'book/inventory_claims.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.ROOT=iso;m.OUT=iso/'book/coverage';assert m.ROOT.is_relative_to(Path('/tmp')) and m.OUT.is_relative_to(iso);m.inventory()
inv=json.loads((m.OUT/'inventory.json').read_text());old=json.loads((ROOT/'book/coverage/inventory.json').read_text());assert old['counts']==inv['counts'];changed={}
for fam in ['exercises','material_source_units']:
 a={r['key']:r for r in old[fam]};b={r['key']:r for r in inv[fam]};assert set(a)==set(b)
 keys=[]
 for k,v in a.items():
  if v['source_text']!=b[k]['source_text']:keys.append(k)
  for n,z in v.items():
   if n not in ['source_text','text_sha256','source_sha256']:assert b[k][n]==z
 changed[fam]=keys
assert changed=={'exercises':[],'material_source_units':['primer-linalg.html::node-141','primer-linalg.html::node-171']},changed
literals={k:{'entire_current':next(r for r in old['material_source_units'] if r['key']==k),'entire_proposed':next(r for r in inv['material_source_units'] if r['key']==k)} for k in changed['material_source_units']}
owner=json.loads((ROOT/'book/coverage/foundations.json').read_text());originalrows=[r for r in owner['material_claims'] if any(k in r['source_unit_keys'] for k in changed['material_source_units'])]
primary=[]
for n,start,end,observation in [
 ('sources/text/roa.txt',122,145,'Assumption1 specifies the1-norm for the Berkenkamp dynamics and policies.'),
 ('sources/text/hertneck.txt',130,210,'Hertneck uses Euclidean state vector norms and infinity input disturbances; equations5–8 mix these norms explicitly.'),
 ('SafeLearning/lyapunov-mpc.html',500,522,'CurrentSource60 explicitly states unadorned robust-MPC vector norms are Euclidean and disturbance input norm is infinity.')]:
 p=ROOT/n;primary.append({'source':ref(p),'line_start':start,'line_end':end,'entire_context':'\n'.join(p.read_text().splitlines()[start-1:end]),'own_observation':observation})
support=Path('/tmp/CompleteFoundationsLiteralCauchySchwarzUses28-draft-v5.lean');actual=Path('/tmp/foundations-literal-cauchy-schwarz-uses7-owner28-trial4.json');native=json.loads(actual.read_text());assert native['actual_exit_code']==0 and native['protection_errors']==[]
proposal={'status':'prospective_source64_exact_three_qualifiers_two_literal_units','author':'Foundations','reader_started_at_utc':started,'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'prospective_source_batch':64,'source64_reserved_by_Root':True,'source64_applied':False,'source':ref(src),'before_inventory':ref(ROOT/'book/coverage/inventory.json'),'before_corrections':ref(ROOT/'book/coverage/material-corrections.json'),'parser':ref(ROOT/'book/inventory_claims.py'),'proposed_source':ref(candidate),'proposed_full29_inventory':ref(m.OUT/'inventory.json'),'exact_replacements':replacements,'exact_inverse_restores_current60_page':True,'all_nodes_tags_attrs_lines_preserved':True,'both_parser_ROOT_and_OUT_isolated':True,'fresh_changed_literal_keys':changed,'counts':inv['counts'],'entire_current_and_proposed_literal_records':literals,'full_current_context_lines120_185':'\n'.join(raw.splitlines()[119:185]),'full_proposed_context_lines120_185':'\n'.join(new.splitlines()[119:185]),'entire_current_owner_claim_rows':originalrows,'full_primary_and_current_module_contexts':primary,'primary_urls':['https://arxiv.org/abs/1705.08551','https://arxiv.org/abs/1806.04167'],'rationale':['A negative radius makes the norm ball empty, so the displayed attained actuator maximum needs an explicit nonnegative radius. The immediately preceding general-ball fact already states r>=0; the new phrase makes the application self-contained.','For j=y the contrast is zero and its norm is zero. The printed sqrt2 contrast norm applies to a distinct class. This qualifier states the intended competitor condition explicitly.','The original parenthesis reads as a blanket claim about every Module11 Lipschitz constant. Berkenkamp uses the1-norm, but currentSource60 robustMPC and Hertneck use Euclidean state/infinity input norms. The qualified sentence names the different contexts while retaining the warning to check norms.'],'actual_mathematical_support':{'full_Uses7_source':ref(support),'actual_TMP_Lean_pass':ref(actual),'source_body_time_unchanged':True,'independent_whole_Uses141_review_pending':True},'whole_units_promoted':[],'new_source_application_or_coverage_claimed':False,'canonical_source_owner_selection_pub_changes':False,'before':before,'after':guard(),'coverage_complete':False}
assert proposal['before']==proposal['after'];path=OUT/'foundations-norm-uses-source64-proposal29-v1.json';path.write_text(json.dumps(proposal,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'proposal':ref(path),'changed_keys':changed,'guards':True}))
