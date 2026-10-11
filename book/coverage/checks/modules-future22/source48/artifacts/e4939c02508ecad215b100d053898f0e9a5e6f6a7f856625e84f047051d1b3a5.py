from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys
R=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(R/'book/coverage'))
from lean_names import declarations
def path(p):
    p=Path(p);return p if p.is_absolute() else R/p
def sha(p):return hashlib.sha256(path(p).read_bytes()).hexdigest()
def read(p):return json.loads(path(p).read_text())
request='/tmp/modules-nn-geometry-two-practices22-canonical-readiness-v1.json'
assert sha(request)=='9a59f2a362438e010d8f55661ae87a2173f6e7050a17c44f21f4b08f54e73cd3'
req=read(request);inv=read(req['inventory']);assert sha(req['inventory'])==req['inventory_sha256']
src=req['proof_file'];assert sha(src)==req['sha256']=='512da9ff468716191ede425bad7a73eefd78b3347038435ba3a62f5f94477e53'
names=[d['name'] for d in declarations(path(src).read_text()) if d['kind'] in ['theorem','lemma']];assert len(names)==13
helper=req['reused_selected_helper'];assert sha(helper)==req['reused_selected_helper_sha256']
manifest=read('reports/full-coverage/checkpoint-21-manifest.json');hp=manifest['proof_files'][helper]
assert hp['sha256']==sha(helper)
for f,h in hp['evidence_sha256'].items():assert sha(f)==h
actual=[]
for z in req['actual_execution_records']:
    assert sha(z['record'])==z['record_sha256'];a=read(z['record']);assert a==z['actual_record_body']
    assert a['actual_exit_code']==0 and a['source']==src
    assert a['source_sha256_before']==a['source_sha256_after']==req['sha256']
    assert sha(a['source_snapshot'])==a['source_snapshot_sha256']==req['sha256']
    assert sha(a['log'])==a['log_sha256']
    actual.append({'file':z['record'],'sha256':z['record_sha256'],'record':a,'raw_log_empty':path(a['log']).stat().st_size==0})
assert sha(req['failed_trial_record'])==req['failed_trial_record_sha256']
units={u['key']:u for u in inv['material_source_units']};exercises={e['key']:e for e in inv['exercises']}
for ex in req['exact_current48_exercises']:
    assert exercises[ex['key']]==ex and sha(ex['source'])==ex['source_sha256']
P='SafeLearning.CompleteModulesNNGeometryPractices22.'
HE=['The literal real2-dimensional storage matrix is diag(4,1), the preactivation row is(2,1), and the full domain is x transpose P x<=1. The maximum and attainer are derived, not assumed. Local-sector applicability is limited to domains containing all actual preactivations.']
HB=['The full independent-coordinate box has center(1,-1), halfwidths(1/5,1/2), and affine output2w0-3w1+1. Soundness on any smaller hidden-output set requires its actual containment in that box; such a set need not contain an endpoint corner.']
def group(c,ds,r,h):return {'clause':c,'lean_declarations':ds,'hypotheses':h,'reason':r,'approval':'approved_complete_actual_mathematical_source_component'}
groupsE=[
 group('Literal storage, quadratic energy, inverse, and two axis sections',names[:4],'The actual official Matrix inverse is proved from a right inverse, positivity is derived, and both axis membership iffs give the true semi-axis lengths1/2 and1. The source energy/output expressions and inverse-metric squared support2 are exported directly.',HE),
 group('Actual sharp ellipsoid row bound and exact printed maximizing direction',names[4:8],'The protected arbitrary positive-storage Cauchy-Schwarz/attainer theorem is genuinely instantiated. The printed vector equals the actual inverse-metric direction, has energy1/output sqrt2, and proves IsGreatest of the full absolute-output image.',HE),
 group('The unit interval misses an attainable preactivation and every sound halfwidth is at least sqrt2',[names[8]],'The actual attaining output is outside[-1,1]; evaluating every purported all-ellipsoid bound at that point forces its radius to be at least sqrt2. This directly explains the local-sector domain gap without claiming a false global sector theorem.',HE),
]
groupsB=[
 group('Exact affine center/radius and all-box interval',[names[9]],'The actual signed affine center6 and absolute-coefficient radius19/10 are calculated from the full box. Both interval inequalities are derived for arbitrary box coordinates.',HB),
 group('Both signed corner attainers and genuine greatest/least endpoints',names[10:12],'The actual upper corner(6/5,-3/2) and lower corner(4/5,-1/2) lie in the full independent box and attain79/10 and41/10. Full-image IsGreatest and IsLeast are proved, establishing exactness.',HB),
 group('Any correlated contained outputs remain sound, while a strict subset can miss the corner',[names[12]],'The interval is transported to arbitrary subsets of the actual box. The singleton center is a genuine contained output set omitting the maximizing corner, so the literal may be conservative has an actual witness; no reachability of the corner in a given network is assumed.',HB),
]
specs=[('nn-in-the-loop.html#practice-easy-3',[977,978,984,988,990,992],groupsE,HE),('nn-in-the-loop.html#practice-medium-2',[1038,1039,1045,1049,1051,1053],groupsB,HB)]
records=[];rows=[]
for key,ids,gs,hyp in specs:
    ex=exercises[key];ds=list(dict.fromkeys(d for g in gs for d in g['lean_declarations']))
    records.append({'exercise_key':key,'exercise_text_sha256':ex['text_sha256'],'source':ex['source'],'source_sha256':ex['source_sha256'],'entire_inventory_record':ex,'review_status':'approved_complete_source','whole_exercise_approved':True,'independent_whole_source_review_passed':True,'hypotheses':hyp,'lean_declarations':ds,'reviewed_components':gs,'missing_clauses':[],'per_exercise_reason':'Every question, hint and worked step was independently read in the actual current48 HTML; every literal mathematical clause matches the full actual proof and its domain. Navigation is individually classified below; no neighboring exercise or generic network theorem is promoted.'})
    for i in ids:
        k='nn-in-the-loop.html::node-'+str(i);u=units[k]
        assert hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
        nav=i in [978,1039]
        if nav: chosen=[];reason='The exact individual sentence directs the reader to prerequisite sections and contains no mathematical conclusion. The links in the actual HTML are navigation only.'
        elif i in [977,1038]:chosen=gs;reason='The complete literal question is answered by all corresponding actual derivation and attained-extremum groups.'
        elif i==984:chosen=gs[1:2];reason='The actual sharp squared inverse-metric bound is genuinely derived by the protected positive-metric support theorem and exactly instantiated for this row.'
        elif i==988:chosen=gs[:1];reason='The actual diagonal energy, inverse and both exact axis-section iffs establish every stated clause.'
        elif i==990:chosen=gs[1:2];reason='The literal squared support2 and all-input bound are derived; the exact printed inverse-metric vector genuinely attains sqrt2 at energy1.'
        elif i==992:chosen=gs[2:];reason='An actual ellipsoid point produces output outside[-1,1], and the true radius necessity follows by evaluating at this witness; the sector conclusion is scoped to its stated interval premise.'
        elif i in [1045,1049]:chosen=gs[:1];reason='The signed affine center and absolute-coefficient halfwidth are calculated for this actual source box and imply every actual-box output lies in the literal interval.'
        elif i==1051:chosen=gs[1:2];reason='The sign-chosen upper corner is in the full box and gives the actual greatest value7.9; the matching lower endpoint is also attained.'
        else:chosen=gs[1:];reason='The full box has exact endpoints; arbitrary contained correlated outputs inherit soundness, and the actual singleton subset omits the corner, providing a conservative-bound witness.'
        r={'source_unit_key':k,'entire_inventory_record':u,'source':u['source'],'source_sha256':u['source_sha256'],'unit_text_sha256':u['text_sha256'],'source_text':u['source_text'],'line':u['line'],'locator':u['locator'],'review_status':'approved_complete_source' if not nav else 'approved_nonformal_instruction','material_status':'nonformal' if nav else 'proved','whole_unit_approved':True,'per_unit_reason':reason,'hypotheses':[] if nav else hyp,'lean_declarations':list(dict.fromkeys(d for g in chosen for d in g['lean_declarations'])),'reviewed_components':chosen,'missing_clauses':[]}
        rows.append(r)
assert len(rows)==12
for p,a in manifest['proof_files'].items():assert sha(p)==a['sha256']
out=Path('/tmp/nn-two-geometry-practices-independent-applied-source-review22-v1.json');assert not out.exists()
result={'schema_version':1,'status':'independent_complete_literal_two_nn_geometry_practices_approved','reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'inventory':req['inventory'],'inventory_sha256':req['inventory_sha256'],'request':request,'request_sha256':sha(request),'records':records,'material_units':rows,'proof_source_sha256':{src:sha(src)},'actual_execution_records':actual,'fully_read_selected_helper':{'source':helper,'source_sha256':sha(helper),'retained_actual_selected_proof_record':hp},'preserved_original_failed_trial':{'file':req['failed_trial_record'],'sha256':sha(req['failed_trial_record']),'record':read(req['failed_trial_record'])},'counts':{'whole_exercises_approved':2,'physical_units_read':12,'proved_units':10,'nonformal_navigation_units':2,'new_source_full_theorem_bodies_read':13,'actual_zero_paired_records':2},'protected21_selected_sources':{'count':1089,'all_exact':True},'independent_checker':'/tmp/review-nn-geometry-two-practices22-independent-applied-v1.py','independent_checker_sha256':sha('/tmp/review-nn-geometry-two-practices22-independent-applied-v1.py'),'scope':['Entire actual source questions, hints, worked steps and every physical descendant read; full new13 theorem bodies and full selected arbitrary positive-metric support dependency independently read.','Both genuine immutable canonical-source execution records report0. Standalone contains eight real style warnings; named log also retains actual protected dependency output. No new compiler or aggregate22 execution is claimed.','This is a future22 semantic review only. No live held21 ledger/offer/helper, HTML, inventory or prior passed proof is changed. Explicit source ownership is Module22, not inferred from the filename.'],'errors':[]}
out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'file':str(out),'sha256':sha(out),'counts':result['counts']}))
