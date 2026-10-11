from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,importlib.util,json,sys,tempfile
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/modules-ibp-zero-sign-source58-proposal28-v1')
SOURCE='SafeLearning/verification.html'
INVENTORY_SHA='82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'
SOURCE_SHA='d01ce44636cd6100bef100a0f466539d61ab6d6c3e8ab64b0d39c7dbdf740f53'
PARSER_SHA='b811c12224b47ec3089f72237600265077b2a46ca93a7eb4cf20ee8d181a140e'
OLD=r'Both inequalities are equalities for $\delta_j = r_j\,\mathrm{sign}(W_{ij})$, which is a feasible corner of the box, so the resulting interval is <em>tight per coordinate</em>:'
NEW=r'Both inequalities are equalities for $\delta_j = r_j\,\mathrm{sign}(W_{ij})$, which is feasible in the box (with $\mathrm{sign}(0)=0$). To obtain a corner, choose either endpoint $\delta_j=\pm r_j$ for each zero-weight entry; those terms still contribute zero. Thus the resulting interval is <em>tight per coordinate</em>:'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def write(p,d):
 with p.open('x') as f:f.write(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
assert not OUT.exists()
source=ROOT/SOURCE;invpath=ROOT/'book/coverage/inventory.json';parser=ROOT/'book/inventory_claims.py';ownerpath=ROOT/'book/coverage/modules.json'
assert sha(source)==SOURCE_SHA and sha(invpath)==INVENTORY_SHA and sha(parser)==PARSER_SHA
inventory=json.loads(invpath.read_bytes());ledger=json.loads(ownerpath.read_bytes())
text=source.read_text();assert text.count(OLD)==1 and NEW not in text
candidate=text.replace(OLD,NEW,1).encode()
assert candidate.count(b'\n')==source.read_bytes().count(b'\n')
assert candidate.decode().replace(NEW,OLD,1).encode()==source.read_bytes()
OUT.mkdir();candidatepath=OUT/'verification-proposed-source58.html'
with candidatepath.open('xb') as f:f.write(candidate)
with tempfile.TemporaryDirectory(prefix='modules-source58-full29-parser-') as td:
 isolated=Path(td);(isolated/'SafeLearning').mkdir()
 for page in (ROOT/'SafeLearning').glob('*.html'):
  target=isolated/'SafeLearning'/page.name
  target.write_bytes(candidate if page==source else page.read_bytes())
 sys.path.insert(0,str(ROOT/'book'))
 spec=importlib.util.spec_from_file_location('modules_source58_isolated_full29_parser',parser)
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 module.ROOT=isolated;module.OUT=isolated/'book/coverage'
 assert module.ROOT.resolve().is_relative_to(Path('/tmp')) and module.OUT.resolve().is_relative_to(module.ROOT)
 assert module.ROOT!=ROOT and module.OUT!=ROOT/'book/coverage'
 module.inventory()
 parsed_bytes=(module.OUT/'inventory.json').read_bytes()
parsed=json.loads(parsed_bytes);proposed_inventory=OUT/'inventory-proposed-source58-v1.json'
with proposed_inventory.open('xb') as f:f.write(parsed_bytes)
assert parsed['counts']==inventory['counts'] and len(parsed['source_sha256'])==29
assert parsed['source_sha256']=={**inventory['source_sha256'],SOURCE:sha(candidatepath)}
changes={};records={}
for field in ['exercises','material_source_units']:
 old={u['key']:u for u in inventory[field]};new={u['key']:u for u in parsed[field]};assert old.keys()==new.keys();changes[field]=[]
 for key in old:
  a=copy.deepcopy(old[key]);b=copy.deepcopy(new[key])
  if a['source']==SOURCE:
   assert b['source_sha256']==sha(candidatepath);a.pop('source_sha256');b.pop('source_sha256')
  if a!=b:
   assert {k:v for k,v in a.items() if k not in ['source_text','text_sha256']}=={k:v for k,v in b.items() if k not in ['source_text','text_sha256']}
   changes[field].append(key);records[key]={'entire_original_inventory_record':old[key],'entire_proposed_inventory_record':new[key]}
assert changes=={'exercises':[],'material_source_units':['verification.html::node-193']}
keys=['verification.html::node-'+str(n) for n in (191,192,193,195,196,1161)]
units={u['key']:u for u in inventory['material_source_units'] if u['key'] in keys}
claims={k:[{'id':c['id'],'status':c['status'],'kind':c['kind'],'statement_in_prose':c['statement_in_prose'],'remaining_gaps':c['remaining_gaps']} for c in ledger['material_claims'] if k in c.get('source_unit_keys',[])] for k in keys}
packet={'status':'tmp_only_source58_zero_weight_sign_corner_precision_proposal_requires_independent_review','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/modules_finish28','prospective_source_batch':58,'source_batch_order':'After Root planned56MPCadopted-domain and57probability-canchange; no canonical application in this preparation.','before_inventory':ref(invpath),'source':ref(source),'parser':ref(parser),'current_modules_owner':ref(ownerpath),'before_raw_fragment':OLD,'after_raw_fragment':NEW,'proposed_source':ref(candidatepath),'proposed_full29_inventory':ref(proposed_inventory),'fresh_parser_changed_text_keys':changes,'full_current_context_lines120_to130':'\n'.join(text.splitlines()[119:130])+'\n','full_proposed_context_lines120_to130':'\n'.join(candidate.decode().splitlines()[119:130])+'\n','current_material_units':units,'current_pending_claims':claims,'entire_changed_records':records,'rationale':'With standard sign(0)=0, a zero-weight coordinate with positive radius is placed at the center by delta=r*sign(W), so the feasible attaining witness is not necessarily a box corner. Either endpoint is a valid replacement in every zero-weight coordinate without changing the row sum.','analytical_counterexample':{'one_dimensional_weight':0,'ordered_box':[-1,1],'center':0,'radius':1,'standard_sign_at_zero':0,'standard_signed_delta':0,'point':0,'box_corners':[-1,1],'reason':'0 is feasible and attains the constant row maximum, but 0 is neither endpoint; changing delta to+1or-1 gives a corner and preserves all weighted terms.'},'formal_work_in_progress':{'source':ref(Path('/tmp/CompleteModulesAffineIBP28-draft-v4.lean')),'limits':'Cumulative standard sign feasible/attainment and true endpoint-corner declarations. Fresh native trial and independent whole review are separate required evidence, not inferred by this parser preparation.'},'exact_reverse_to_entire_current_source_bytes':True,'all_other28_pages_and_all_other_literal_records_unchanged':True,'both_parser_ROOT_and_OUT_isolated':True,'coverage_or_lean_compiler_or_live_write_claimed':False,'limits':['Ex15.1 current worked formula only says feasible and may close independently after actual standardSign bridge review.','Node193 whole stays pending until corrected exact literal is independently reviewed and Root later applies source58 and corresponding identities.','Node196 whole is excluded: monotone activation, general zonotope, independence, attribution and broad depth assertions need separate proof/review.','TMP candidate parses all29pages; all556exercises/all12774material inventory shapes preserved.','Root alone handles canonical source/owner/selection/publication/Git changes.']}
write(OUT/'modules-ibp-zero-sign-source58-proposal28-v1.json',packet)
assert sha(source)==SOURCE_SHA and sha(invpath)==INVENTORY_SHA and sha(parser)==PARSER_SHA
print(json.dumps({'status':packet['status'],'proposal':ref(OUT/'modules-ibp-zero-sign-source58-proposal28-v1.json'),'changed':changes}))
