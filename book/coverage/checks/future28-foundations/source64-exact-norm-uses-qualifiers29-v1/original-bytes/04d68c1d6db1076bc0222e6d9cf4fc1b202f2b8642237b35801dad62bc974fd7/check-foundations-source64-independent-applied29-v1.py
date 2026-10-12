from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,importlib.util,sys,tempfile
R=Path('/home/oxrexkevin/SafetyBased');req=Path('/tmp/foundations-norm-uses-source64-proposal29-v1/foundations-norm-uses-source64-proposal29-v1.json');C=Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(q):p=Path(q['file']);return p if p.is_absolute() else R/p
def ref(p):p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
ctx=json.loads(C.read_bytes());pins={**ctx['pins_sha256'],**ctx['held_current_source_sha256']}
def guard():
 for n,h in pins.items():assert sha(R/n)==h,n
before={str(R/n):sha(R/n) for n in pins};guard();d=json.loads(req.read_bytes());assert sha(req)=='dfc2ed59376406e6b336b61b7b3cd57314c881eb3ddf0a95339caad48e4508a2';assert d['source64_applied'] is False and d['prospective_source_batch']==64
closed={str(req):sha(req),str(C):sha(C),str(Path(__file__)):sha(__file__)}
def add(q):
 if isinstance(q,dict):p=path(q);assert sha(p)==q['sha256']
 else:p=Path(q)
 closed[str(p)]=sha(p);return ref(p)
for k in ['source','before_inventory','before_corrections','parser','proposed_source','proposed_full29_inventory']:add(d[k])
raw=path(d['source']).read_text();proposed=path(d['proposed_source']).read_text();forward=raw
assert len(d['exact_replacements'])==3
for q in d['exact_replacements']:assert forward.count(q['before'])==1;forward=forward.replace(q['before'],q['after'])
assert forward==proposed and len(raw.splitlines())==len(proposed.splitlines())
inverse=proposed
for q in reversed(d['exact_replacements']):assert inverse.count(q['after'])==1;inverse=inverse.replace(q['after'],q['before'])
assert inverse==raw
assert d['full_current_context_lines120_185']=='\n'.join(raw.splitlines()[119:185]);assert d['full_proposed_context_lines120_185']=='\n'.join(proposed.splitlines()[119:185])
sys.path.insert(0,str(R/'book'));from validate import Document
assert [(n.tag,n.attrs,n.line) for n in Document(raw).nodes]==[(n.tag,n.attrs,n.line) for n in Document(proposed).nodes]
for q in d['full_primary_and_current_module_contexts']:
 add(q['source']);src=path(q['source']).read_text();assert q['entire_context']=='\n'.join(src.splitlines()[q['line_start']-1:q['line_end']])
assert 'with respect to the 1-norm' in (R/'sources/text/roa.txt').read_text()
assert 'kf (x, u + d) − f (x, u)k ≤ λkdk∞' in (R/'sources/text/hertneck.txt').read_text()
assert 'Unadorned vector norms here are Euclidean' in (R/'SafeLearning/lyapunov-mpc.html').read_text()
add(d['actual_mathematical_support']['full_Uses7_source']);add(d['actual_mathematical_support']['actual_TMP_Lean_pass']);support=json.loads(path(d['actual_mathematical_support']['actual_TMP_Lean_pass']).read_bytes());assert type(support['actual_exit_code']) is int and support['actual_exit_code']==0 and support['protection_errors']==[]
for k in ['raw_log','source_snapshot']:add(support[k])
prior=Path('/tmp/foundations-norm-csuses24-independent-applied-full-source-review28-v1.json');add(prior)
base=json.loads((R/'book/coverage/inventory.json').read_bytes());author=json.loads(path(d['proposed_full29_inventory']).read_bytes())
iso=Path(tempfile.mkdtemp(prefix='applied-source64-independent-full29-',dir='/tmp'));(iso/'SafeLearning').mkdir()
for p in (R/'SafeLearning').glob('*.html'):
 (iso/'SafeLearning'/p.name).write_bytes(proposed.encode() if p.name=='primer-linalg.html' else p.read_bytes())
assert len(list((iso/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('applied_source64_fresh_parser',R/'book/inventory_claims.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);mod.ROOT=iso;mod.OUT=iso/'book/coverage';assert mod.ROOT.resolve().is_relative_to(Path('/tmp')) and mod.OUT.resolve().is_relative_to(iso);mod.inventory()
fresh=json.loads((mod.OUT/'inventory.json').read_bytes());assert fresh['counts']==base['counts']==author['counts'];changed={}
for family in ['exercises','material_source_units']:
 oldmap={r['key']:r for r in base[family]};newmap={r['key']:r for r in fresh[family]};authmap={r['key']:r for r in author[family]};assert set(oldmap)==set(newmap)==set(authmap);assert newmap==authmap
 changed[family]=[]
 for key,o in oldmap.items():
  n=newmap[key]
  if o['source_text']!=n['source_text']:changed[family].append(key)
  for field,value in o.items():
   if field not in ['source_text','text_sha256','source_sha256']:assert n[field]==value,(key,field)
  if o['source']!='SafeLearning/primer-linalg.html':assert o==n,key
assert changed=={'exercises':[],'material_source_units':['primer-linalg.html::node-141','primer-linalg.html::node-171']}==d['fresh_changed_literal_keys']
for key,pair in d['entire_current_and_proposed_literal_records'].items():assert pair['entire_current']==next(r for r in base['material_source_units'] if r['key']==key) and pair['entire_proposed']==next(r for r in fresh['material_source_units'] if r['key']==key)
add(mod.OUT/'inventory.json');add('/tmp/foundations-source64-preparation29-actual-v1.json');add('/tmp/foundations-source64-preparation29-actual-v1.log');add('/tmp/prepare-foundations-source64-qualifiers29-v1.py');add('/tmp/run-foundations-source64-qualifiers29-v1.py')
guard();assert before=={str(R/n):sha(R/n) for n in pins}
out=Path('/tmp/foundations-source64-independent-applied-findings29-v1.json');assert not out.exists();out.write_text(json.dumps({'status':'passed_independent_source64_full_narrow_wording_and_isolated_full29_parser_review','reviewer':'/root/applied_next','review_completed_at_utc':datetime.now(timezone.utc).isoformat(),'proposal':ref(req),'source64_applied':False,'replacement_count':3,'exact_forward_and_inverse':True,'all_node_tags_attrs_lines_equal':True,'changed_literal_keys':changed,'all556_exercises_unchanged':True,'material_count':fresh['counts']['material_source_units'],'fresh_independent_full29_inventory':ref(mod.OUT/'inventory.json'),'both_ROOT_OUT_strictly_TMP':True,'narrow_wording_decisions':[{'clause':'umax nonnegative support bound','approved':True,'reason':'Makes the actual attained ball maximum domain explicit; zero radius and zero objective remain included.'},{'clause':'distinct competitor j!=y','approved':True,'reason':'Makes the actual sqrt2 coordinate contrast norm valid; excludes the zero self-contrast.'},{'clause':'Module11 norm conventions','approved':True,'reason':'Primary Berkenkamp Assumption1 states one-norm dynamics/policy bounds. Hertneck and actual source60 use Euclidean state and infinity input disturbance bounds. The qualifier states these separate contexts faithfully.'}],'prospective_corrected141_whole_association':'The exact proposed141 is covered by all seven full bodies independently approved in prior24 peer, under page line69 Euclidean convention. This is a prospective literal association only; current141 remains pending until actual64.','generic_p_less_one_or_whole171_approval_inferred':False,'no_owner_source_proof_selection_or_publication_mutation':True,'closed_evidence_sha256':closed,'errors':[]},indent=2,ensure_ascii=False)+'\n');print(json.dumps({'findings':ref(out),'changed':changed,'guarded':True}))
