from pathlib import Path
import json,hashlib,re,datetime
ROOT=Path('/home/oxrexkevin/SafetyBased')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def resolve(s):
 p=Path(s);return p if p.is_absolute() else ROOT/p
def ref(p):return {'file':str(p),'sha256':H(p)}
def chk(r):
 p=resolve(r['file']);assert H(p)==r['sha256'],str(p);return p
reqpath=Path('/tmp/foundations-coercivity-margin24-single-literal-full-source-review-request-v1.json')
assert H(reqpath)=='d4e6077b5491749d18f3e4d82ab141e8a12ad03de0a218c4520be90150532909'
r=json.loads(reqpath.read_text())
inv=json.loads(chk(r['current_inventory']).read_text())
page=chk(r['source_page']);lines=page.read_text().splitlines(keepends=True)
ctx=r['complete_source_context'];assert ''.join(lines[ctx['lines_start']-1:ctx['lines_end']])==ctx['exact_lines']
row=r['material_units'][0];assert row==next(x for x in inv['material_source_units'] if x['key']==row['key'])
assert row['key']=='primer-basics.html::node-1150'
source=chk(r['new_actual_source']);body=source.read_text();assert body==r['entire_source_and_all_seven_theorem_bodies']
assert not re.search(r'\b(sorry|admit|axiom)\b',body)
names=['SafeLearning.CompleteFoundationsCoercivityMargin24.'+n for n in re.findall(r'^theorem\s+(\w+)',body,re.M)]
assert len(names)==7 and names==r['new_public_theorem_names']
record=json.loads(chk(r['actual_standalone_record']).read_text());assert record==r['entire_original_actual_record']
assert record['actual_exit_code']==0 and record['actual_command']==['lake','env','lean',str(source)]
assert record['actual_workdir']==str(ROOT/'verification/lean')
assert record['source_sha256_before']==record['source_sha256_after']==H(source)
assert chk(r['actual_standalone_raw_log']).read_bytes()==b''
assert record['raw_log_sha256']==r['actual_standalone_raw_log']['sha256']
chk(r['actual_runner']);assert H(record['actual_runner'])==record['actual_runner_sha256']
failed=[]
for old in r['actual_failed_histories']:
 rec=json.loads(chk(old['record']).read_text());assert rec==old['entire_actual_record'] and rec['actual_exit_code']==1
 oldsrc=chk(old['source_snapshot']);oldlog=chk(old['raw_log'])
 assert H(oldsrc)==rec['source_sha256_before']==rec['source_sha256_after']
 assert H(oldlog)==rec['raw_log_sha256'] and oldlog.read_bytes()
 failed.append(old)
assert len(failed)==1
selected=r['direct_selected_dependency'];dep=chk(selected['source']);assert dep.read_text()==selected['entire_source_body']
assert 'actual_closed_coercive_minimum' in selected['entire_source_body']
for p,d in selected['original22_selected_proof_row']['evidence_sha256'].items():assert H(ROOT/p)==d,p
primary=[]
for c in r['direct_primary_mathlib_contexts']:
 p=chk(c['source']);ll=p.read_text().splitlines(keepends=True)
 assert ''.join(ll[c['lines_start']-1:c['lines_end']])==c['exact_lines']
 primary.append(c)
manifest=json.loads(chk(r['protected_selected22_manifest']).read_text())
assert len(manifest['proof_files'])==1113
for p,d in manifest['proof_files'].items():assert H(ROOT/p)==d['sha256'],p
chk(r['held_foundation23_final39_offer'])
# These old ledger fingerprints remain original measured trial observations;
# they are not reinterpreted as a new current-ledger assertion during Root23 integration.
components=[
 {'clause':'Norm-coercivity, compact closed sublevels and attained minimum on every closed nonempty S','lean_declarations':names[:3], 'reason':'For arbitrary proper normed space, actual threshold-by-norm growth derives the cocompact restricted limit. For a sublevel c, growth at c+1 bounds it inside an actual compact K, while continuity and closed S make the sublevel closed. The selected generic closed-coercive minimum then gives an actual IsMinOn witness, not an assumed minimizer.'},
 {'clause':'Squared-displacement affine safety filter on any nonempty halfspace, without boundedness','lean_declarations':names[3:5], 'reason':'For every nominal, reverse triangle inequality derives growth of actual squared displacement. The true affine halfspace is closed by inner-product continuity; its inherited nonemptiness and derived coercivity yield a genuine attained optimizer. No compactness/boundedness of the halfspace is assumed.'},
 {'clause':'Nonzero linear objective on all real Euclidean controls is unbounded above and has no maximizer','lean_declarations':[names[5]], 'reason':'For every real M, the explicit scalar multiple ((M+1)/inner(b,b))*b has objective M+1 because b!=0 gives strictly positive self-inner product. This constructs arbitrarily high feasible points and contradicts any all-space maximum.'},
 {'clause':'Strictly positive attained minimum on every nonempty compact K excluding0','lean_declarations':[names[6]], 'reason':'Actual compact attainment gives x in K. Since0 is excluded, positive definiteness yields V(x)>0; the proof exposes an actual IsLeast of the image, preserving V(0)=0. No positive margin premise is assumed.'}
]
hyp=[
 'The complete local section is finite-dimensional Euclidean space R^n; the general norm-coercivity statements use a proper normed additive group, a legitimate more general domain containing all such Euclidean spaces. S is closed and nonempty, f continuous, and actual norm-coercivity is the quantified threshold condition printed in the source.',
 'The safety-filter feasible halfspace is nonempty, inherited from the same paragraph’s preceding closed/nonempty-S condition. The statement does not assert feasibility of an inconsistent constraint. Arbitrary real a, vector b and nominal control are allowed; boundedness is not required. The real inner-product definition equals the printed Euclidean dot product.',
 'The no-maximum linear objective has b!=0. For the positive-margin clause, V is continuous, V(0)=0 and V(x)>0 for x!=0; K is compact, nonempty and excludes0.'
]
unit={'source_unit_key':row['key'],'entire_inventory_record':row,'unit_text_sha256':row['text_sha256'],'source_sha256':row['source_sha256'],'review_status':'independent_whole_source_review_passed','material_status':'proved','whole_unit_approved':True,'lean_declarations':names,'hypotheses':hyp,'per_unit_reason':'Every mathematical clause of the full coercivity/safety-filter/nonattainment/positive-margin paragraph matches a genuine derived theorem under the local finite-dimensional and inherited nonempty-feasible-set scope. The compact-sublevel step is directly proved rather than inferred from an unrelated numeric example.','components':components,'missing_clauses':[]}
report={'status':'independent_whole_literal_source_review_passed','reviewed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/applied_next','request':ref(reqpath),'current_inventory':r['current_inventory'],'source_page':r['source_page'],'material_units':[unit],'proof_sources':[r['new_actual_source'],selected['source']],'actual_standalone_record':r['actual_standalone_record'],'entire_original_actual_record':record,'actual_raw_log':r['actual_standalone_raw_log'],'actual_runner':r['actual_runner'],'preserved_actual_failed_histories':failed,'complete_local_context':ctx,'direct_selected_dependency':selected,'direct_primary_mathlib_contexts':primary,'protected_selected22_manifest':r['protected_selected22_manifest'],'protected_selected22_source_count':1113,'all1113_selected_sources_exact':True,'held_foundation23_final39_offer':r['held_foundation23_final39_offer'],'checker':ref(Path(__file__)),'scope':'Fresh TMP-only future24 full-literal review. Retains original measured trial conditions and source bytes; no fresh Lean execution, named build, canonical selection, current owner ledger amendment, aggregate24 or deployment asserted. Current Root23 installation is outside this review; old trial22 ledger observations remain historical.'}
out=Path('/tmp/foundations-coercivity-margin24-single-literal-independent-applied-review-v1.json');assert not out.exists();out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'review':str(out),'sha256':H(out),'whole_unit_approved':True,'theorems':len(names),'protected_sources':1113}))
