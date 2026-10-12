from pathlib import Path
from fractions import Fraction
from datetime import datetime,timezone
import hashlib,importlib.util,json,re,sys,tempfile
sys.dont_write_bytecode=True
ROOT=Path('/home/oxrexkevin/SafetyBased')
PACKET=Path('/tmp/modules-integral-tracking-precision-unnumbered31-v1/modules-integral-tracking-three-precision-phrases-unnumbered-full29-proposal31-v1.json')
OUT=Path('/tmp/modules-integral-tracking-three-precision-independent-foundations31-v1')
assert not OUT.exists();OUT.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(r):return Path(r['file']) if Path(r['file']).is_absolute() else ROOT/r['file']
def check(r):
 p=path(r);assert sha(p)==r['sha256'],str(p)
 if 'bytes' in r:assert p.stat().st_size==r['bytes']
 return p
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(PACKET)=='b82bee43c596907f19989fa103219d9f0b0b54b98c49a0999bea2cf1f4e8dad5'
d=json.loads(PACKET.read_bytes());assert d['source_number_reserved'] is False and d['source_applied'] is False
direct=['source','before_inventory','before_corrections','parser','validator','proposed_source',
 'original_installed_owner30_candidate','proposed_full29_inventory','actual_parser_stdout',
 'actual_supporting_full35_source','actual_supporting_passed_trial12','actual_supporting_snapshot','actual_supporting_raw_log']
inputs=[PACKET]+[check(d[k]) for k in direct]
old=check(d['source']).read_text();new=check(d['proposed_source']).read_text()
assert check(d['source']).read_bytes()==(ROOT/d['live_source_original_path']).read_bytes()
replacements=[{'before':r'\xi=-0.833','after':r'\xi=-5/6\approx-0.833'},
 {'before':'spectral radius $0.632$ ($b=1$)','after':r'spectral radius $\sqrt{2/5}\approx0.632$ ($b=1$)'},
 {'before':'and $0.616$ ($b=1.2$)','after':r'and $\sqrt{19/50}\approx0.616$ ($b=1.2$)'}]
assert d['exact_replacements']==replacements
forward=old
for x in replacements:
 assert forward.count(x['before'])==1;forward=forward.replace(x['before'],x['after'])
assert forward==new
inverse=new
for x in reversed(replacements):
 assert inverse.count(x['after'])==1;inverse=inverse.replace(x['after'],x['before'])
assert inverse==old and old.count('\n')==new.count('\n')
sys.path.insert(0,str(ROOT/'book'))
from validate import Document
assert [(n.tag,n.attrs,n.line) for n in Document(old).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
assert d['full_current_context_lines1008_1030']==''.join(old.splitlines(keepends=True)[1007:1030])
assert d['full_proposed_context_lines1008_1030']==''.join(new.splitlines(keepends=True)[1007:1030])
owner=json.loads(check(d['original_installed_owner30_candidate']).read_bytes())
assert sha(check(d['original_installed_owner30_candidate']))==sha(ROOT/'book/coverage/modules.json')
ex=next(x for x in owner['exercises'] if x['inventory_key']=='nn-in-the-loop.html::exercise-19')
assert ex==d['exact_current_owned_exercise_body'] and ex['status']=='pending'
rows=[x for x in owner['material_claims'] if 'nn-in-the-loop.html::node-1247' in x['source_unit_keys']]
assert rows==d['exact_current_owned_changed_material_rows']
body=check(d['actual_supporting_full35_source']).read_text()
public=re.findall(r'^theorem\s+(\w+)',body,re.M)
assert len(public)==35 and len(set(public))==35
assert all(name in public for name in d['exact_support_names'])
assert 'def integralEquilibrium (b d r : ℝ) : ℝ := ((1-b)*r/2-d)/(b/5)' in body
assert 'def nominalNetwork (r x : ℝ) : ℝ := r/2-(3/10)*Real.tanh (x-r)' in body
native=json.loads(check(d['actual_supporting_passed_trial12']).read_bytes())
assert type(native['actual_exit_code']) is int and native['actual_exit_code']==native['actual_runner_exit_code']==0
assert native['protection_errors']==[] and native['source_sha256_before']==native['source_sha256_after']==sha(check(d['actual_supporting_full35_source']))
assert native['source_snapshot_sha256']==sha(check(d['actual_supporting_snapshot'])) and native['raw_log_sha256']==sha(check(d['actual_supporting_raw_log']))
assert native['actual_command']==['lake','env','lean',native['source']] and native['actual_workdir']==str(ROOT/'verification/lean')
headers=len(re.findall(r'^.*:\d+:\d+: warning:',check(d['actual_supporting_raw_log']).read_text(),re.M))
assert abs(Fraction(-5,6)-Fraction(-833,1000))<Fraction(1,2000)
for square,display in [(Fraction(2,5),Fraction(632,1000)),(Fraction(19,50),Fraction(616,1000))]:
 assert (display-Fraction(1,2000))**2<square<(display+Fraction(1,2000))**2
assert ((1-Fraction(6,5))*1/2-Fraction(1,10))/(Fraction(6,5)/5)==Fraction(-5,6)
author_native=Path('/tmp/modules-integral-tracking-precision-unnumbered31-preparation-actual-v1.json')
author=json.loads(author_native.read_bytes());assert type(author['actual_exit_code']) is int and author['actual_exit_code']==0 and author['protection_errors']==[]
author_files=[author_native,author_native.with_suffix('.log'),Path('/tmp/prepare-modules-integral-tracking-precision-unnumbered31-v1.py'),Path('/tmp/run-modules-integral-tracking-precision-unnumbered31-preparation-v1.py')]
inputs+=author_files
selected=ROOT/'verification/lean/SafeLearning/CompleteModulesTanhChords.lean'
assert selected.exists();inputs.append(selected)
iso=Path(tempfile.mkdtemp(prefix='integral-tracking-independent-full29-',dir='/tmp'));(iso/'SafeLearning').mkdir()
for p in (ROOT/'SafeLearning').glob('*.html'):
 (iso/'SafeLearning'/p.name).write_bytes(check(d['proposed_source']).read_bytes() if str(p.relative_to(ROOT))==d['live_source_original_path'] else p.read_bytes())
assert len(list((iso/'SafeLearning').glob('*.html')))==29
spec=importlib.util.spec_from_file_location('independent_integral_precision31_parser',ROOT/'book/inventory_claims.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.ROOT=iso;m.OUT=iso/'book/coverage'
assert m.ROOT.is_relative_to(Path('/tmp')) and m.OUT.is_relative_to(iso)
m.inventory();fresh=m.OUT/'inventory.json';a=json.loads(check(d['before_inventory']).read_bytes());b=json.loads(fresh.read_bytes())
assert a['counts']==b['counts']==d['parser_counts']
changed={}
for family in ['exercises','material_source_units']:
 aa={r['key']:r for r in a[family]};bb={r['key']:r for r in b[family]};assert set(aa)==set(bb);changed[family]=[]
 for k,x in aa.items():
  if x['source_text']!=bb[k]['source_text']:changed[family].append(k)
  for f,v in x.items():
   if f not in ['source_text','text_sha256','source_sha256']:assert bb[k][f]==v,(k,f)
  if x['source']!=d['live_source_original_path']:assert x==bb[k]
  if k in d['entire_current_and_proposed_literal_records']:
   assert x==d['entire_current_and_proposed_literal_records'][k]['entire_current']
   assert bb[k]==d['entire_current_and_proposed_literal_records'][k]['entire_proposed']
assert changed==d['fresh_changed_literal_keys']=={'exercises':['nn-in-the-loop.html::exercise-19'],'material_source_units':['nn-in-the-loop.html::node-1247']}
assert {k for k in a['source_sha256'] if a['source_sha256'][k]!=b['source_sha256'][k]}=={d['live_source_original_path']}
result={'status':'passed_independent_full_integral_tracking_three_precision_phrases_and_fresh_isolated_full29_parser_review',
 'errors':[],'reviewer':'/root/foundations_recovery28','request':ref(PACKET),
 'source':d['source'],'proposed_source':d['proposed_source'],'exact_replacements':replacements,
 'full_current_and_proposed_literals_and_contexts_read':True,'exact_forward_and_inverse':True,
 'all_tags_attributes_and_lines_unchanged':True,'independent_parser':{'both_ROOT_and_OUT_strictly_TMP':True,
  'entire_full29_inventory':ref(fresh),'changed_text_keys':changed,'all_other28_pages_and_other_literal_texts_exact':True},
 'full_relevant_supporting_bodies_read':d['exact_support_names'],
 'additional_used_support_private_body_read':'actual_complex_conjugate_pair_has_exact_norm',
 'manual_mathematical_assessment':[
  'With b=6/5,d=1/10,r=1, the actual implemented integral equilibrium ((1-b)r/2-d)/(b/5) equals-5/6. Its distance from-.833 is1/3000<.0005.',
  'The full Frechet derivative and coordinate-matrix action prove the actual Jacobian, not an unrelated fixture. Nominal trace6/5/det2/5 give complete roots3/5±i/5; the perturbed trace57/50/det19/50 give57/100±i sqrt551/100.',
  'The true complete spectrum, complex norm identities and attained IsGreatest norm-image bodies derive radii sqrt(2/5) and sqrt(19/50). Independent exact rational squared brackets certify the original.632/.616 displays within.0005.',
  'Only the three exact/approximate-display phrases change. Equilibrium/stability/convergence/all-reference attribution and every other clause are unchanged; their full whole35/Exercise14.5 correspondence remains a separate review.'],
 'actual_supporting_source_and_final_native':{'source':d['actual_supporting_full35_source'],'native':d['actual_supporting_passed_trial12'],
  'snapshot':d['actual_supporting_snapshot'],'raw_log':d['actual_supporting_raw_log'],'original_native_body_and_times_unchanged':True,
  'actual_exit_code':0,'emitted_diagnostic_warning_headers':headers},
 'original_author_actual_preparation':ref(author_native),'original_author_body_time_preserved':True,
 'source_ordinal_reserved_or_applied':False,'whole35_or_whole_current_or_prospective_exercise_approval_inferred':False,
 'compiler_or_current_owner_or_canonical_or_publication_mutation':False,'coverage_complete':False,
 'all_direct_inputs_sha256':{str(p):sha(p) for p in inputs},'actual_fresh_inventory':ref(fresh)}
target=OUT/'integral-tracking-three-precision-independent-foundations31-semantic-peer-v1.json'
target.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'peer':ref(target),'changed_text_keys':changed,'whole_exercise_approved':False}))
