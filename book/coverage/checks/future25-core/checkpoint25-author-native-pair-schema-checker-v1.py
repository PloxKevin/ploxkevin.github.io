from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,sys
ROOT=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(ROOT/'book/coverage'))
helper=ROOT/'book/coverage/prepare_checkpoint25_selection_v1.py';ns={'__name__':'author_native_schema_fixture_only','__file__':str(helper)};exec(compile(ast.parse(helper.read_text()),str(helper),'exec'),ns)
from lean_names import declarations
paths={'core':'book/coverage/checks/future25-core/core-audit25-candidate-source52-material-additions-v1-reviewed.json','foundations':'book/coverage/checks/foundations-future25/source52/foundations-audit25-candidate-source52-additions-v1-reviewed.json','applied':'book/coverage/checks/applied-future25/source52/applied-audit25-candidate-source52-additions-v1.json','modules':'book/coverage/checks/modules-future25/source52/modules-audit25-candidate-source52-additions-v1-reviewed.json'}
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();sources={};counts={};whole={}
for owner,n in paths.items():
 d=json.loads((ROOT/n).read_text());counts[owner]=len(d['proof_files']);names=[]
 for f,r in d['proof_files'].items():
  assert f not in sources;assert h(ROOT/f)==r['sha256'];record=ns['standalone_success'](f,r['sha256'],r['evidence_sha256']);sources[f]={'sha256':r['sha256'],'actual_standalone_record':record};names.extend(x['name'] for x in declarations((ROOT/f).read_text()) if x['kind'] in ('theorem','lemma'))
 whole[owner]=len(names)
assert counts=={'core':1,'foundations':2,'applied':7,'modules':2} and sum(whole.values())==90
p=ROOT/'book/coverage/checks/future25-core/checkpoint25-author-native-pair-schema-observation-v1.json';assert not p.exists();p.write_text(json.dumps({'status':'author_read_only_native12_pair_schema_observation_passed_not_independent_review','checked_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(helper.relative_to(ROOT)),'sha256':h(helper)},'owner_source_counts':counts,'owner_public_export_counts':whole,'new_sources':sources,'actual_production_selector_executed':False,'scope':'Author syntax/native pair function checks only; no Root binding, integration, plan, production selection, aggregate or independent code approval inferred.'},indent=2)+'\n');print(json.dumps({'native_sources':len(sources),'public_exports':sum(whole.values()),'schema_observation':str(p.relative_to(ROOT)),'sha256':h(p)}))
