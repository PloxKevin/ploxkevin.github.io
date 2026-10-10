from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,copy,re
R=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/modules21-final-mapping-independent-applied-confirmation-v1.json');SELF=Path('/tmp/check-modules21-final-independent-applied-v1.py')
assert not OUT.exists();started=datetime.now(timezone.utc).isoformat();cache={}
def sha(n):
 p=Path(n);p=p if p.is_absolute() else R/p;s=p.stat();k=(str(p),s.st_size,s.st_mtime_ns)
 if k not in cache:cache[k]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[k]
def read(n):return json.loads((R/n).read_text())
def ref(r):assert sha(r['file'])==r['sha256'],r;return read(r['file'])
OP='book/coverage/checks/modules-audit21-source48-additions-v1.json';oh=sha(OP);assert oh=='d0ee132585b2942141986a979aca055e0c8035c33f9634b965832ef8a79ac862';o=read(OP)
held={n:sha(n) for n in (OP,o['module_ledger'],o['module_builder'],o['binding_validator'],o['review_mapping']['file'],o['unchanged_literal_identity_sidecar']['file'])}
assert o['proof_files']=={} and o['counts']['new_owned_proof_files']==0
for k,hk in [('module_ledger','module_ledger_sha256'),('module_builder','module_builder_sha256'),('binding_validator','binding_validator_sha256')]:assert sha(o[k])==o[hk]
ledger=read(o['module_ledger']);mapping=ref(o['review_mapping']);side=ref(o['unchanged_literal_identity_sidecar']);proofs=ref(o['proof_selection_manifest'])['files'];assert len(proofs)==12
inv=read(o['current_inventory']);assert sha(o['current_inventory'])==o['current_inventory_sha256']==sha('book/coverage/inventory.json')
oldinv=ref(side['historical_inventory']);assert side['current_inventory']=={'file':o['current_inventory'],'sha256':o['current_inventory_sha256']}
for n,x in side['historical_owner_assets'].items():assert sha(x['preserved'])==x['sha256']
old=read(side['historical_owner_assets']['book/coverage/modules.json']['preserved'])
owned={}
for section in ['exercises','material_source_units']:
 a={r['key']:r for r in oldinv[section] if r['source'] in old['scope_pages']};b={r['key']:r for r in inv[section] if r['source'] in old['scope_pages']}
 assert a==b=={r['key']:r for r in side['unchanged_owned_literals'][section]};assert side['changed_owned_literals_excluded'][section]==[];owned[section]=len(a)
for n,h in side['source_sha256'].items():assert sha(n)==h
aliases=ref(mapping['canonical_path_aliases'])['aliases']
def resolve(n):
 if n in aliases:return aliases[n]['path']
 p=Path(n)
 if p.is_absolute() and str(p).startswith(str(R)+'/'):return str(p.relative_to(R))
 return n
supplied={}
for x in o['explicit_cross_owner_proof_offers']:
 s=ref(x)
 for n,p in s['proof_files'].items():assert n not in supplied;supplied[n]=p
assert set(supplied)==set(proofs)==set(o['cross_owner_required_proof_sources'])
assert {n:p for n,p in ledger['proof_files'].items() if n not in proofs}==old['proof_files']
assert ledger['declarations'][:len(old['declarations'])]==old['declarations']
ns={};exec(compile((R/'book/coverage/lean_names.py').read_text(),str(R/'book/coverage/lean_names.py'),'exec'),ns)
actual=[];public=[]
for n,p in proofs.items():
 assert sha(n)==p['sha256']==supplied[n]['sha256'];names=[x['name'] for x in ns['declarations']((R/n).read_text()) if x['kind'] in ('theorem','lemma')];assert names==p['declarations'];public+=names
 assert ledger['proof_files'][n]['declarations']==names
 x=o['cross_owner_required_proof_sources'][n];assert x['public_exports']==names and x['proof_selection_owner']==p['proof_offer_owner'] and x['explicit_proof_offer']==p['explicit_proof_offer']
 for kind,mk,hk in [('standalone','compiler_manifest','compiler_manifest_sha256'),('named','named_manifest','named_manifest_sha256')]:
  f=p[mk];assert sha(f)==p[hk];r=read(f);assert r['exit_code']==0 and r['source_sha256_before']==r['source_sha256_after']==sha(n);assert resolve(r['source'])==n
  assert sha(resolve(r['log']))==r['log_sha256'];assert r['started_at_utc'] and r['finished_at_utc']
  if r.get('source_snapshot'):assert sha(resolve(r['source_snapshot']))==sha(n)
  actual.append({'source':n,'kind':kind,'record':f,'sha256':p[hk],'actual_exit_code':0,'raw_log':resolve(r['log']),'raw_log_sha256':r['log_sha256'],'started_at_utc':r['started_at_utc'],'finished_at_utc':r['finished_at_utc']})
assert len(public)==89 and len(set(public))==89 and [x['name'] for x in ledger['declarations'][len(old['declarations']):]]==public
for n,p in ledger['proof_files'].items():
 ev=p['standalone_compile_evidence'];assert sha(n)==p['sha256']==ev['sha256'] and ev['exit_code']==0 and ev['source_unchanged'];assert sha(resolve(ev['log']))==ev['log_sha256']
ex={x['key']:x for x in inv['exercises']};unit={x['key']:x for x in inv['material_source_units']};le={x['inventory_key']:x for x in ledger['exercises']};lc={x['id']:x for x in ledger['material_claims']};oe={x['inventory_key']:x for x in old['exercises']};oc={x['id']:x for x in old['material_claims']};mes=set();mus=set();reviewbind=[]
assert o['source_reviews']==[b['review'] for b in mapping['reviews']]
known={d['name'] for d in ledger['declarations']}
for b in mapping['reviews']:
 rv=ref(b['review']);rr=b['review'];assert rv['reviewed_at_utc']==rr['original_review_time'];assert rv.get('reviewed_by',rv.get('reviewer'))==rr['reviewer'];original={r['exercise_key']:r for r in rv.get('reviewed_exercises',rv.get('records'))};ou={r['source_unit_key']:r for e in original.values() for r in e['material_units']}
 for e in b['exercises']:
  k=e['key'];assert k not in mes;mes.add(k);a=original[k];i=ex[k];assert a['whole_exercise_approved'] is True and a['missing_clauses']==[];assert a['source_text']==i['source_text'];assert e['text_sha256']==a['exercise_text_sha256']==i['text_sha256']
  assert e['lean_declarations']==a['lean_declarations'] and e['hypotheses']==a['hypotheses'];assert e['reviewed_clauses']==a.get('reviewed_clauses',a.get('reviewed_components'))
  row=le[k];c=row['claims'];assert row['status']=='complete_math' and row['independent_whole_source_review']==rr and len(c)==1;c=c[0]
  assert c['status']=='proved' and c['statement_in_prose']==i['source_text'] and c['lean_declarations']==e['lean_declarations'] and c['hypotheses']==e['hypotheses'] and c['correspondence']==e['reason'] and c['remaining_gaps']==[] and c['independent_source_review']==rr and c['scope_limits']==b['limits']
 for u in b['material_units']:
  k=u['key'];assert k not in mus;mus.add(k);a=ou[k];i=unit[k];assert a['source_text']==i['source_text'];assert u['text_sha256']==a['unit_text_sha256']==i['text_sha256'];assert u['source_sha256']==a['source_sha256']==i['source_sha256'];assert a['missing_clauses']==[]
  assert u['status']=={'proved':'proved','not_formalizable':'not_a_formal_claim','not_a_formal_claim':'not_a_formal_claim'}[a['material_status']];assert u['lean_declarations']==a['lean_declarations'] and u['hypotheses']==a['hypotheses'] and u['reason']==a['per_unit_reason']
  c=lc[k+'::claim-review'];assert c['status']==u['status'] and c['statement_in_prose']==i['source_text'] and c['lean_declarations']==u['lean_declarations'] and c['hypotheses']==u['hypotheses'] and c['correspondence']==u['reason'] and c['remaining_gaps']==[] and c['independent_source_review']==rr and c['scope_limits']==b['limits']
 reviewbind.append({'review':rr,'exercises':len(b['exercises']),'material_units':len(b['material_units']),'whole_decisions_and_original_times_exact':True})
assert len(mes)==17 and len(mus)==94
for e in ledger['exercises']:
 k=e['inventory_key'];assert e['source_sha256']==ex[k]['source_sha256'] and e['source_text_sha256']==ex[k]['text_sha256']
 if k not in mes:
  a=copy.deepcopy(e);a.pop('source48_unchanged_literal_identity');assert a==oe[k],k
for c in ledger['material_claims']:
 k=c['id']
 if k not in {u+'::claim-review' for u in mus}:
  a=copy.deepcopy(c);a.pop('source48_unchanged_literal_identity');assert a==oc[k],k
# Calculate the complete import closure independently; no filename-based owner inference.
visited=set()
def visit(n):
 if n in visited:return
 visited.add(n)
 for name in re.findall(r'^\s*import\s+(SafeLearning\.[A-Za-z0-9_.]+)',(R/n).read_text(),re.M):visit('verification/lean/'+name.replace('.','/')+'.lean')
for n in ledger['proof_files']:visit(n)
deps={n:sha(n) for n in sorted(visited-set(ledger['proof_files']))};assert deps==ledger['required_external_import_dependencies']==o['required_external_import_dependencies']
dm=ref(o['canonical_dependency_manifest'])
for n,p in dm['artifacts'].items():assert sha(n)==p['sha256']
build=ref(o['actual_builder']);assert build['actual_exit_code']==0 and build['resulting_module_ledger_sha256']==sha(o['module_ledger']);assert sha(build['log'])==build['log_sha256']
for n,h in build['helper_sha256_before'].items():assert sha(n)==h==build['helper_sha256_after'][n]
globalr=ref(o['actual_global_validator']);assert globalr['errors']==[];gexec=ref(o['actual_global_validator_execution']);assert gexec['actual_exit_code']==0 and gexec['result']=={'file':o['actual_global_validator']['file'],'sha256':o['actual_global_validator']['sha256']}
protections={}
for num,np,ni in [(19,1055,14101),(20,1068,30207)]:
 p=f'reports/full-coverage/checkpoint-{num}-manifest.json';m=read(p);assert len(m['proof_files'])==np and len(m['frozen_inputs_sha256'])==ni
 for n,x in m['proof_files'].items():
  assert sha(n)==x['sha256']
  for a,h in x['evidence_sha256'].items():assert sha(a)==h
 for a,h in m['frozen_inputs_sha256'].items():assert sha(str(Path(m['snapshot'])/a))==h
 protections[str(num)]={'manifest':p,'sha256':sha(p),'sources':np,'frozen_inputs':ni,'all_exact':True}
assert all(sha(n)==h for n,h in held.items())
d={'schema_version':1,'status':'independent_final_module21_source48_mapping_mechanics_passed','reviewed_by':'/root/applied_next','started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'independent_checker':str(SELF),'independent_checker_sha256':sha(SELF),'exact_offer':{'file':OP,'sha256':oh},'held_owner_assets':held,'counts':{'whole_exercises':len(mes),'individually_reviewed_physical_units':len(mus),'unchanged_owned_inventory_records':owned,'unchanged_old_proof_rows':len(old['proof_files']),'explicit_cross_owner_sources':len(proofs),'new_public_exports':len(public),'genuine_retained_actual_zero_records':len(actual),'exact_external_import_dependencies':len(deps),'exact_canonical_dependency_artifacts':len(dm['artifacts'])},'original_review_bindings':reviewbind,'actual_compiler_records':actual,'protected_checkpoints':protections,'actual_builder':o['actual_builder'],'actual_global_validator':o['actual_global_validator'],'limits':['This is an independent readonly mechanical check of the final owner mapping and explicit supplied proof offers. Existing full semantic review decisions and original timestamps remain byte-exact; no new mathematical approval is inferred from normalization.','No owner builder, proof compiler, browser capture or aggregate was rerun by this checker. Previously genuine actual-zero compiler/build/validator records are hash-bound, including retained warning logs.','No held Module21/Applied21/Foundation21 ledger, helper, offer, HTML or inventory was mutated. New report/helper are unique TMP artifacts.'],'errors':[]}
OUT.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'output':str(OUT),'sha256':sha(OUT),'status':d['status'],'counts':d['counts'],'protected':protections},indent=2))
