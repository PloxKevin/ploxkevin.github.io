"""Add the independently whole-reviewed LFT exercise to a NEW isolated candidate."""
from pathlib import Path
from datetime import datetime,timezone
import copy,collections,hashlib,json,re
from lean_names import declarations
R=Path(__file__).resolve().parents[2];B='book/coverage/checks/modules-future23/source51'
H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest();J=lambda n:json.loads((R/n).read_text());ref=lambda n:{'file':n,'sha256':H(n)}
def put(n,v):
 p=R/n;assert not p.exists(),n;p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def main():
 oldname=B+'/modules23-candidate-source51-identity-v1.json';assert H(oldname)=='65e7566b3f3c315ae4cc2297606fe74f8a7136e28d0d4a47ca9cd46fe1b41fbd';old=J(oldname)
 inpname=B+'/lft/lft-source51-input-bindings-v1.json';assert H(inpname)=='ef9aa484215f8d5358de7968a851ba79d857b69157b7cd33cf6cbf7077c42c83';inp=J(inpname)
 assert H(inp['inventory'])==inp['inventory_sha256']==H('book/coverage/inventory.json');inv=J(inp['inventory']);es={x['key']:x for x in inv['exercises']};us={x['key']:x for x in inv['material_source_units']}
 for n,d in inp['protected_selected22_and_owner_sha256'].items():assert H(n)==d,n
 aliases=J(inp['canonical_path_aliases']['file'])['aliases'];assert H(inp['canonical_path_aliases']['file'])==inp['canonical_path_aliases']['sha256']
 for row in aliases.values():assert H(row['path'])==row['sha256']
 review=inp['original_review'];rv=J(review['path']);assert H(review['path'])==review['sha256'] and rv==inp['entire_original_review_body_and_time'] and rv['reviewed_at_utc']==review['original_review_time']
 assert rv['whole_exercise_approved'] and rv['remaining_gaps']==[] and rv['errors']==[]
 key=inp['whole_exercise_key'];assert rv['entire_original_exercise_record']==es[key]
 out=copy.deepcopy(old);row=next(x for x in out['exercises'] if x['inventory_key']==key);assert row['status']=='pending';retained=[c for c in row['claims'] if c['status'] in ('proved','not_a_formal_claim')]
 reviewref={'file':review['path'],'sha256':review['sha256'],'reviewer':review['reviewer'],'original_review_time':review['original_review_time']}
 row['claims']=retained+[{'id':key+'::source51-independent-whole23-lft','statement_in_prose':es[key]['source_text'],'kind':'independently_reviewed_whole_exercise','status':'proved','lean_declarations':rv['lean_declarations'],'hypotheses':rv['hypotheses'],'correspondence':rv['correspondence'],'remaining_gaps':[],'source_unit_keys':inp['material_unit_keys'],'independent_source_review':reviewref,'scope_limits':rv['limits']}]
 row['status']='complete_math';row['independent_whole_source_review']=reviewref
 units={c['id']:c for c in out['material_claims']}
 for u in rv['material_units']:
  k=u['source_unit_key'];assert u['whole_unit_approved'] and u['missing_clauses']==[] and u['entire_inventory_record']==us[k] and u['material_status']=='proved'
  target=units[k+'::claim-review'];prior=copy.deepcopy(target)
  target.update(statement_in_prose=us[k]['source_text'],status='proved',kind='independently_reviewed_mathematical_source_unit',lean_declarations=u['lean_declarations'],hypotheses=u['hypotheses'],correspondence=u['per_unit_reason'],remaining_gaps=[],independent_source_review=reviewref,scope_limits=rv['limits'])
  target['prior_source51_claim_body_preserved']=prior
 newpaths=[];names=[];imports={}
 for proof in inp['proof_files']:
  n=proof['source'];assert H(n)==proof['sha256'] and n not in out['proof_files'];text=(R/n).read_text();decls=declarations(text);public=[d['name'] for d in decls if d['kind'] in ('theorem','lemma')];assert public==proof['public_declarations'];pairs=proof['actual_paired_records']
  for pair,mode in zip(pairs,['lean_standalone','named_lean_module_build']):
   a=J(pair['actual_record']['path']);assert H(pair['actual_record']['path'])==pair['actual_record']['sha256'] and a['actual_exit_code']==0 and a['kind']==mode and a['source_unchanged'] is True
   assert a['source_sha256_before']==a['source_sha256_after']==H(n) and H(pair['raw_log']['path'])==pair['raw_log']['sha256']==a['log_sha256'] and H(pair['source_snapshot']['path'])==pair['source_snapshot']['sha256']==H(n)
   assert aliases[a['log']]['path']==pair['raw_log']['path'] and aliases[a['source_snapshot']]['path']==pair['source_snapshot']['path']
  stand=pairs[0];out['proof_files'][n]={'sha256':H(n),'selection_scope':'independently_whole_reviewed_module23_lft_new_source','proof_selection_owner':'Modules23','standalone_compile_status':'passed','standalone_compile_evidence':{'file':n,'sha256':H(n),'exit_code':0,'source_unchanged':True,'log':stand['raw_log']['path'],'log_sha256':stand['raw_log']['sha256'],'compiler_manifest':stand['actual_record']['path'],'compiler_manifest_sha256':stand['actual_record']['sha256']},'actual_paired_records':pairs,'declarations':public}
  for name in public:
   m=re.search(r'^\s*(?:theorem|lemma)\s+'+re.escape(name.rsplit('.',1)[1])+r'\b',text,re.M);assert m
   out['declarations'].append({'name':name,'file':n,'line':text[:m.start()].count('\n')+1,'statement':text[m.start():].split(':=',1)[0].strip()})
  for module in re.findall(r'^import\s+(SafeLearning\.\S+)',text,re.M):
   path='verification/lean/'+module.replace('.','/')+'.lean';imports[path]=H(path)
  newpaths.append(n);names+=public
 assert len(names)==len(set(names))==16 and len(newpaths)==2
 for n,d in imports.items():
  if n not in newpaths:out['required_external_import_dependencies'][n]=d
 out['generated_at_utc']=datetime.now(timezone.utc).isoformat();out['reviewed_lft23_source51_candidate_extension']={'original_reviewed_source51_identity_candidate':ref(oldname),'input_bindings':ref(inpname),'fresh_whole_exercise':key,'fresh_material_units':inp['material_unit_keys'],'original_whole_review':reviewref,'new_source_files':newpaths,'new_public_theorem_exports':names,'required_safelearning_import_sha256':imports,'scope':'Distinct isolated candidate extension only; original seven whole decisions and identity layers remain exact. Full original semantic peer/time retained; canonical companion pair evidence is separately bound.'}
 out['counts']={'exercises':len(out['exercises']),'exercise_status':dict(collections.Counter(e['status'] for e in out['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status'] for e in out['exercises'] for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status'] for c in out['material_claims'])),'new_declarations':len(out['declarations'])}
 olde={x['inventory_key']:x for x in old['exercises']};oldu={x['id']:x for x in old['material_claims']};changedunits={k+'::claim-review' for k in inp['material_unit_keys']}
 for e in out['exercises']:
  if e['inventory_key']!=key:assert e==olde[e['inventory_key']]
 for c in out['material_claims']:
  if c['id'] not in changedunits:assert c==oldu[c['id']]
 assert {n:r for n,r in out['proof_files'].items() if n not in newpaths}==old['proof_files'] and out['declarations'][:len(old['declarations'])]==old['declarations']
 for n,d in inp['protected_selected22_and_owner_sha256'].items():assert H(n)==d,n
 target=B+'/modules23-candidate-source51-lft-v2.json';put(target,out)
 guard=B+'/modules23-source51-lft-candidate-binding-integrity-v2.json';put(guard,{'status':'passed_exact_isolated_lft_source51_extension_candidate','candidate':ref(target),'original_source51_candidate':ref(oldname),'input_bindings':ref(inpname),'fresh_exercise_key':key,'fresh_material_unit_keys':inp['material_unit_keys'],'original_review':reviewref,'counts':{'new_whole_exercises':1,'new_physical_units':6,'new_sources':2,'new_public_theorems':16,'original_exercise_bodies_preserved':216,'original_material_bodies_preserved':len(old['material_claims'])-6,'original_proof_rows_preserved':len(old['proof_files'])},'required_safelearning_import_sha256':imports,'no_live_ledger_or_html_write':True,'scope':'Actual isolated candidate construction only; independent final delta mechanics and Root live global validation/aggregate23 remain separate.'})
 print(json.dumps({'candidate':ref(target),'integrity':ref(guard),'counts':out['counts']}))
if __name__=='__main__':main()
