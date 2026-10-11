"""Add two exactly reviewed geometry exercises to the preserved isolated NN candidate."""
from pathlib import Path
from datetime import datetime,timezone
import copy,json,hashlib,collections,re
from lean_names import declarations
ROOT=Path(__file__).resolve().parents[2]
BASE='book/coverage/checks/modules-future22/source48'
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def read(n):return json.loads((ROOT/n).read_text())
def put(n,obj):
    p=ROOT/n;assert not p.exists();p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
def build():
    inp=read(BASE+'/nn-geometry-two-practices-input-bindings-v3.json')
    prev=inp['previous_reviewed_candidate_offer'];assert sha(prev['file'])==prev['sha256'];offer=read(prev['file'])
    assert sha(offer['module_ledger'])==offer['module_ledger_sha256'];prior=read(offer['module_ledger']);out=copy.deepcopy(prior)
    for n,r in inp['baseline_owner_assets'].items():assert sha(n)==sha(r['preserved'])==r['sha256']
    old=read(inp['baseline_owner_assets']['book/coverage/modules.json']['preserved'])
    assert sha('book/coverage/inventory.json')==sha(inp['inventory'])==inp['inventory_sha256']
    inv=read(inp['inventory']);es={r['key']:r for r in inv['exercises']};us={r['key']:r for r in inv['material_source_units']}
    ref=inp['review'];assert sha(ref['file'])==ref['sha256'];rv=read(ref['file']);assert rv['reviewed_at_utc']==ref['original_review_time']
    aliases=read(inp['canonical_path_aliases']['file'])['aliases'];assert sha(inp['canonical_path_aliases']['file'])==inp['canonical_path_aliases']['sha256']
    for original,a in aliases.items():assert sha(a['path'])==a['sha256']
    refs=inp['actual_execution_records']
    for ref in refs:
        a=ref['record'];assert sha(a['file'])==a['sha256'];r=read(a['file']);assert r['actual_exit_code']==0 and r['source_sha256_before']==r['source_sha256_after']==sha(inp['source'])
        assert aliases[r['log']]['path']==ref['raw_log']['path'];assert sha(ref['raw_log']['path'])==r['log_sha256']==ref['raw_log']['sha256'];assert sha(ref['source_snapshot']['path'])==sha(inp['source'])
    el={r['inventory_key']:r for r in out['exercises']};ul={r['id']:r for r in out['material_claims']};mapped=[];mappedu=[]
    reviewref={'file':inp['review']['file'],'sha256':inp['review']['sha256'],'original_review_time':rv['reviewed_at_utc'],'reviewer':rv['reviewer']}
    for e in rv['records']:
        k=e['exercise_key'];assert e['whole_exercise_approved'] and e['missing_clauses']==[] and e['entire_inventory_record']==es[k]
        row=el[k];row['claims']=[{'id':k+'::source48-independent-whole22','statement_in_prose':es[k]['source_text'],'kind':'independently_reviewed_whole_exercise','status':'proved','lean_declarations':e['lean_declarations'],'hypotheses':e['hypotheses'],'correspondence':e['per_exercise_reason'],'remaining_gaps':[],'source_unit_keys':[],'independent_source_review':reviewref,'scope_limits':rv['scope']}];row['status']='complete_math';row['independent_whole_source_review']=reviewref;mapped.append(k)
    for u in rv['material_units']:
        k=u['source_unit_key'];assert u['entire_inventory_record']==us[k] and u['missing_clauses']==[] and u['whole_unit_approved']
        st={'proved':'proved','nonformal':'not_a_formal_claim'}[u['material_status']]
        ul[k+'::claim-review'].update(statement_in_prose=us[k]['source_text'],status=st,kind='independently_reviewed_mathematical_source_unit' if st=='proved' else 'instruction_or_navigation',lean_declarations=u['lean_declarations'],hypotheses=u['hypotheses'],correspondence=u['per_unit_reason'],remaining_gaps=[],independent_source_review=reviewref,scope_limits=rv['scope']);mappedu.append(k)
    assert len(mapped)==2 and len(mappedu)==12 and len(set(mappedu))==12
    text=(ROOT/inp['source']).read_text();names=[r['name'] for r in declarations(text) if r['kind'] in ('theorem','lemma')];assert len(names)==13
    assert inp['source'] not in out['proof_files'];stand=refs[0]
    out['proof_files'][inp['source']]={'sha256':sha(inp['source']),'selection_scope':'independently_whole_reviewed_module22_owned_new_source','proof_selection_owner':'Modules22','standalone_compile_status':'passed','standalone_compile_evidence':{'file':inp['source'],'sha256':sha(inp['source']),'exit_code':0,'log':stand['raw_log']['path'],'log_sha256':stand['raw_log']['sha256'],'source_unchanged':True,'compiler_manifest':stand['record']['file'],'compiler_manifest_sha256':stand['record']['sha256']},'declarations':names}
    for name in names:
        m=re.search(r'^\s*theorem\s+'+re.escape(name.rsplit('.',1)[1])+r'\b',text,re.M);assert m
        out['declarations'].append({'name':name,'file':inp['source'],'line':text[:m.start()].count('\n')+1,'statement':text[m.start():].split(':=',1)[0].strip()})
    pe={r['inventory_key']:r for r in prior['exercises']};pu={r['id']:r for r in prior['material_claims']}
    for row in out['exercises']:
        if row['inventory_key'] not in mapped:assert row==pe[row['inventory_key']]
    for row in out['material_claims']:
        if row['id'] not in {k+'::claim-review' for k in mappedu}:assert row==pu[row['id']]
    assert {k:v for k,v in out['proof_files'].items() if k!=inp['source']}==prior['proof_files'];assert out['declarations'][:len(prior['declarations'])]==prior['declarations']
    combined_e=offer['fresh_whole_exercise_keys']+mapped;combined_u=offer['fresh_material_unit_keys']+mappedu
    out['generated_at_utc']=datetime.now(timezone.utc).isoformat();out['reviewed_work_integration22_combined_candidate_v3']={'geometry_input_bindings':{'file':BASE+'/nn-geometry-two-practices-input-bindings-v3.json','sha256':sha(BASE+'/nn-geometry-two-practices-input-bindings-v3.json')},'previous_reviewed_candidate_offer':prev,'baseline21_owner_assets':inp['baseline_owner_assets'],'additional_whole_exercises':mapped,'additional_material_units':mappedu,'fresh_whole_exercises':combined_e,'fresh_material_units':combined_u,'original_geometry_review':reviewref,'scope':'The two original scalar wholes and every prior row remain exact; two independently reviewed geometry wholes are appended in a new isolated candidate. No live21 assets are written.'}
    out['counts']={'exercises':len(out['exercises']),'exercise_status':dict(collections.Counter(x['status'] for x in out['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status'] for e in out['exercises'] for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status'] for c in out['material_claims'])),'new_declarations':len(out['declarations'])}
    sel=read('reports/full-coverage/checkpoint-21-selection.json')
    for n,p in sel['proof_files'].items():assert sha(n)==p['sha256']
    target=BASE+'/modules22-candidate-v3.json';put(target,out)
    guard={'status':'exact_four_whole_twenty_four_literal_candidate_bindings_and_held21_preservation_passed','candidate_ledger':target,'candidate_ledger_sha256':sha(target),'source48_inventory':inp['inventory'],'source48_inventory_sha256':inp['inventory_sha256'],'previous_reviewed_candidate_offer':prev,'original_geometry_whole_review':reviewref,'baseline_owner_assets':inp['baseline_owner_assets'],'additional_whole_exercises':mapped,'additional_material_units':mappedu,'fresh_whole_exercises':combined_e,'fresh_material_units':combined_u,'counts':{'whole_exercises':4,'physical_units':24,'old_exercises_preserved':len(old['exercises'])-4,'old_material_preserved':len(old['material_claims'])-24,'old_proof_rows_preserved':len(old['proof_files']),'new_source_files':2,'new_theorems':22,'selected21_source_hashes_checked':len(sel['proof_files'])},'canonical_geometry_path_aliases':inp['canonical_path_aliases'],'additional_actual_paired_execution':refs,'live_owner_mutated':False,'limits':'Candidate binding validation is not a global ledger pass or checkpoint22 aggregate audit.'}
    g=BASE+'/candidate-binding-integrity-v3.json';put(g,guard)
    for n,r in inp['baseline_owner_assets'].items():assert sha(n)==r['sha256']
    print(json.dumps({'ledger':target,'ledger_sha256':sha(target),'guard':g,'guard_sha256':sha(g),'counts':out['counts']}));return out
if __name__=='__main__':build()
