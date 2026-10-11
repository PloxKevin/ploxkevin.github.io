"""Close actual independent screenshot observations without changing browser26."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
ROOT=Path('/home/oxrexkevin/SafetyBased')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
catalog=ROOT/'reports/full-coverage/browser-corrections-26-inputs.json'
browser=ROOT/'reports/full-coverage/browser-checkpoint-26.json'
manual=ROOT/'reports/full-coverage/source53-six-paragraph-content-manual-review26-v1.json'
held={str(p):sha(p) for p in (catalog,browser,manual)}
specs=[
('/tmp/root-browser26-captures0-to11-actual-manual-review-v1.json','e852d8ae6ae597680c2414e49e481caf5123a5398ca232e7e76dee9b584e0db3','observations','alias_index'),
('/tmp/browser26-screenshot-indices12-24-independent-foundations-capture-region-review-v1.json','8b90b960b41e1e829fa233ad1dc89a41cfc4a05a0b23a702828de1986294d5d5','image_records','index'),
('/tmp/modules-browser26-screenshots24-35-actual-manual-review-v1.json','bd30fa4dbb199b111f6cc08d3f0c229de55822be0a715f45f0a1214a36cf6355','captures','screenshot_alias_index'),
('/tmp/applied-browser26-aliases36-to47-actual-manual-observations-v1.json','3c706818cbad3dbdd276928e3d2ebdc1b1083f2788b617722f28d54af57d1bd6','screenshots','screenshot_alias_index_zero_based')]
aliases=json.loads(catalog.read_text())['screenshot_aliases'];assert len(aliases)==48
observed={};originals=[];limits=[]
for slot,(name,h,key,indexkey) in enumerate(specs):
 p=Path(name);assert sha(p)==h;body=json.loads(p.read_text());rows=body[key];assert len(rows)==12
 assert {r[indexkey] for r in rows}==set(range(slot*12,(slot+1)*12))
 originals.append({'file':name,'sha256':h,'original_body_with_all_review_times_unchanged':body})
 for row in rows:
  i=row[indexkey];assert i not in observed;a=aliases[i]
  ref=row['image'] if slot==0 else row
  assert ref['file']==a['file'] and ref['sha256']==a['sha256']==sha(ROOT/a['file'])
  assert sha(ROOT/a['original'])==a['sha256']
  observed[i]={'index':i,'image':{'file':a['file'],'sha256':a['sha256']},'original_alias':a['original'],'review_record':{'file':name,'sha256':h},'original_observation_body_unchanged':row}
  limited=(bool(row['visible_limitation']) if slot==0 else row['captured_region_review_status']!='passed_captured_region_readability_only' if slot==1 else row['viewport_width']==390 if slot==2 else row['static_capture_formula_limit'])
  if limited:limits.append(i)
assert set(observed)==set(range(48))
assert held=={str(p):sha(p) for p in (catalog,browser,manual)}
out=Path('/tmp/root-browser26-all48-actual-captured-region-review-closure27-v1.json');assert not out.exists()
report={'status':'all48_actual_captured_region_inspections_closed_with_formula_visibility_limits',
 'closed_at_utc':datetime.now(timezone.utc).isoformat(),'closure_helper':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},
 'native_browser_inputs':{'file':str(catalog.relative_to(ROOT)),'sha256':sha(catalog)},
 'original_browser26_and_scoped_manual6_unchanged_sha256':held,'actual_image_count':48,
 'review_records_original_bodies_and_times_unchanged':originals,'observations':[observed[i] for i in range(48)],
 'mobile_static_formula_visibility_limit_indices':sorted(limits),
 'horizontal_scroll_manually_verified':False,'whole_pages_or_mathematical_proofs_approved':False,
 'all_formulas_visible_in_static_mobile_captures':False,
 'scope':'All 48 exact saved content-region captures were actually viewed by four reviewers. This closes their observation records only. Several wide mobile equations extend beyond the static crop; scrolling and off-screen formula readability remain unverified by these image observations. Existing automated browser26, its historical all48 pending metadata, six-paragraph manual record, source/assets, and frozen26 evidence remain unchanged. No new browser execution, math approval, coverage promotion or publication is implied.'}
with out.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print(json.dumps({'file':str(out),'sha256':sha(out),'actually_inspected':48,'formula_visibility_limits':limits}))
