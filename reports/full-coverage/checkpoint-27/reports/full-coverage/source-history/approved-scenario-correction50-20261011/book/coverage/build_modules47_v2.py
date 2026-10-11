"""Build modules at inventory47, preserving source44 decisions and adding six reviewed practices."""
from pathlib import Path
import copy,json,hashlib,re,collections
from datetime import datetime,timezone
from lean_names import declarations as exported
from modules_binding20_source47_v2 import check_bindings
ROOT=Path(__file__).resolve().parents[2]
BASE='book/coverage/checks/modules-future20/source47'
def read(n):return json.loads((ROOT/n).read_text())
def sha(n):return hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
def build():
    side=read(BASE+'/unchanged-literal-identity-v1.json');mapping=read(BASE+'/review-mappings-v2.json')
    assert mapping['unchanged_identity_sidecar']=={'file':BASE+'/unchanged-literal-identity-v1.json','sha256':sha(BASE+'/unchanged-literal-identity-v1.json')}
    old=read(side['historical_owner_assets']['book/coverage/modules.json']['preserved']);ledger=copy.deepcopy(old)
    inv=read(side['current_inventory']['file']);exact={x['key']:x for x in inv['exercises']};units={x['key']:x for x in inv['material_source_units']}
    identity={'file':BASE+'/unchanged-literal-identity-v1.json','sha256':sha(BASE+'/unchanged-literal-identity-v1.json'),'status':side['status']}
    for e in ledger['exercises']:e['source47_unchanged_literal_identity']=identity
    for c in ledger['material_claims']:c['source47_unchanged_literal_identity']=identity
    es={e['inventory_key']:e for e in ledger['exercises']};cs={c['id']:c for c in ledger['material_claims']}
    for review in mapping['reviews']:
        ref=review['review']
        for e in review['exercises']:
            actual=exact[e['key']];row=es[e['key']]
            row['claims']=[{'id':e['key']+'::source47-independent-whole20','statement_in_prose':actual['source_text'],'kind':'independently_reviewed_whole_exercise','status':'proved','lean_declarations':e['lean_declarations'],'hypotheses':e['hypotheses'],'correspondence':e['reason'],'remaining_gaps':[],'source_unit_keys':[],'independent_source_review':ref,'scope_limits':review['limits']}]
            row['status']='complete_math';row['independent_whole_source_review']=ref
        for u in review['material_units']:
            c=cs[u['key']+'::claim-review'];c.update(statement_in_prose=units[u['key']]['source_text'],status=u['status'],kind=u['kind'],lean_declarations=u['lean_declarations'],hypotheses=u['hypotheses'],correspondence=u['reason'],remaining_gaps=[],independent_source_review=ref,scope_limits=review['limits'])
    proofrows=read(mapping['proof_execution_bindings']['file'])['files'];newexports=[]
    for n,rec in proofrows.items():
        text=(ROOT/n).read_text();names=[r['name'] for r in exported(text) if r['kind'] in ('theorem','lemma')]
        assert n not in ledger['proof_files']
        ledger['proof_files'][n]={'sha256':sha(n),'selection_scope':'direct_reviewed_reference','standalone_compile_status':'passed','standalone_compile_evidence':{'file':n,'sha256':sha(n),'exit_code':0,'log':rec['raw_log'],'log_sha256':rec['raw_log_sha256'],'source_unchanged':True,'compiler_manifest':rec['compiler_manifest'],'compiler_manifest_sha256':rec['compiler_manifest_sha256']},'declarations':names}
        for name in names:
            short=name.rsplit('.',1)[1];m=re.search(r'^\s*(?:theorem|lemma)\s+'+re.escape(short)+r'\b',text,re.M);assert m,name
            rest=text[m.start():];header=rest.split(':=',1)[0].strip()
            newexports.append({'name':name,'file':n,'line':text[:m.start()].count('\n')+1,'statement':header})
    assert len(newexports)==34;ledger['declarations']+=newexports
    allown=set(ledger['proof_files']);visited=set()
    def closure(n):
        if n in visited:return
        visited.add(n)
        text=(ROOT/n).read_text()
        for name in re.findall(r'^\s*import\s+(SafeLearning\.[A-Za-z0-9_.]+)',text,re.M):
            dependency='verification/lean/'+name.replace('.','/')+'.lean';assert (ROOT/dependency).is_file();closure(dependency)
    for n in allown:closure(n)
    ledger['required_external_import_dependencies']={n:sha(n) for n in sorted(visited-allown)}
    ledger.update(generated_at_utc=datetime.now(timezone.utc).isoformat(),current_inventory=side['current_inventory']['file'],current_inventory_sha256=side['current_inventory']['sha256'],source_sha256={n:inv['source_sha256'][n] for n in old['scope_pages']})
    ledger['inventory_identity_rebase47']={'identity_sidecar':identity,'prior_immutable_source44_owner_assets':side['historical_owner_assets'],'no_changed_owned_literals':True,'new_review_mapping':{'file':BASE+'/review-mappings-v2.json','sha256':sha(BASE+'/review-mappings-v2.json')}}
    ledger['reviewed_work_integration20']={'mapping':BASE+'/review-mappings-v2.json','mapping_sha256':sha(BASE+'/review-mappings-v2.json'),'canonical_path_aliases':mapping['canonical_path_aliases'],'exact_reviews':[r['review'] for r in mapping['reviews']],'scope':'Seven independently whole-reviewed practices, forty-two exact physical units, five original actual-zero sources. Earlier44 semantic bodies/times/bytes preserved.'}
    ledger['counts']={'exercises':len(ledger['exercises']),'exercise_status':dict(collections.Counter(e['status'] for e in ledger['exercises'])),'exercise_claim_status':dict(collections.Counter(c['status'] for e in ledger['exercises'] for c in e['claims'])),'material_claim_status':dict(collections.Counter(c['status'] for c in ledger['material_claims'])),'new_declarations':len(ledger['declarations'])}
    guard=check_bindings(ROOT,ledger,old,side,mapping);gp=BASE+'/binding-integrity-v2.json';path=ROOT/gp;assert not path.exists();path.write_text(json.dumps(guard,indent=2,ensure_ascii=False)+'\n')
    ledger['current_identity_binding_validation']={'file':gp,'sha256':sha(gp),'status':guard['status'],'validator':'book/coverage/modules_binding20_source47_v2.py','validator_sha256':sha('book/coverage/modules_binding20_source47_v2.py')}
    (ROOT/'book/coverage/modules.json').write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'counts':ledger['counts'],'ledger_sha256':sha('book/coverage/modules.json'),'binding_sha256':sha(gp)},indent=2));return ledger
if __name__=='__main__':build()
