from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, importlib.util, shutil, sys

R=Path('/home/oxrexkevin/SafetyBased')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
REF=lambda p:{'file':str(p),'sha256':H(p)}
P=Path('/tmp/modules-conformal-source55-precision-proposal-v1.json')
assert H(P)=='7d75117fb9aef0240dea8326b9b76c480b424e4880e9c1b0fd2a29dc517b2ee5'
d=json.loads(P.read_text());page=R/d['current_source53']['file'];candidate=Path(d['candidate_only']['file'])
assert H(page)==d['current_source53']['sha256'] and H(candidate)==d['candidate_only']['sha256']
assert H(R/d['current_inventory']['file'])==d['current_inventory']['sha256']
before=page.read_text();after=candidate.read_text();assert len(d['exact_replacements'])==1
x=d['exact_replacements'][0]
assert before.count(x['before'])==after.count(x['after'])==1
assert '\n' not in x['before']+x['after']
assert before.replace(x['before'],x['after'],1)==after and after.replace(x['after'],x['before'],1)==before
assert before.count('\n')==after.count('\n')
assert H(d['helper']['file'])==d['helper']['sha256']
old=d['original_full_source_review'];assert H(old['record']['file'])==old['record']['sha256']
assert json.loads(Path(old['record']['file']).read_text())==old['entire_original_body_and_time']
lex=d['actual_lexicographic_seed_trial'];assert H(lex['record']['file'])==lex['record']['sha256']
la=json.loads(Path(lex['record']['file']).read_text());assert la==lex['entire_original_body_and_time']
assert type(la['actual_exit_code']) is int and la['actual_exit_code']==0 and la['protection_errors']==[]
assert H(la['source'])==H(la['source_snapshot'])==la['source_sha256_before']==la['source_sha256_after']
assert H(la['raw_log'])==la['raw_log_sha256']
primary=R/d['primary_original']['file'];assert H(primary)==d['primary_original']['sha256']
plines=primary.read_text().splitlines()
assert '\n'.join(plines[2701:2774])+'\n'==d['primary_scope']['exact_excerpt']
pt=primary.read_text();start=pt.index('Theorem D.1 (Conformal calibration coverage guarantee)');end=pt.index('Proof. See Theorem 2.2 of [83].',start)+len('Proof. See Theorem 2.2 of [83].')
fullprimary=pt[start:end];assert 'distinct with probability 1' in fullprimary and 'continuous\njoint distribution' in fullprimary
assert '\n'.join(before.splitlines()[829:845])+'\n'==d['full_original_parent_html_excerpt']
assert '\n'.join(after.splitlines()[829:845])+'\n'==d['full_proposed_parent_html_excerpt']
assert '\n'.join(before.splitlines()[397:437])+'\n'==d['full_original_section5_html_excerpt']
sys.path.insert(0,str(R/'book'));from validate import Document
a,b=Document(before),Document(after)
assert len(a.nodes)==len(b.nodes) and a.ids==b.ids
assert [(n.tag,n.attrs,n.line)for n in a.nodes]==[(n.tag,n.attrs,n.line)for n in b.nodes]
SIM=Path('/tmp/foundations-independent-conformal-source55-full29-parser-v1');assert not SIM.exists()
(SIM/'SafeLearning').mkdir(parents=True)
html=list((R/'SafeLearning').glob('*.html'));assert len(html)==29
for q in html:shutil.copyfile(q,SIM/'SafeLearning'/q.name)
(SIM/d['current_source53']['file']).write_text(after)
parser=R/'book/inventory_claims.py';spec=importlib.util.spec_from_file_location('foundations_conformal55_inventory',parser);g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
g.ROOT=SIM;g.OUT=SIM/'book/coverage';assert g.ROOT!=R and g.OUT.resolve().is_relative_to(SIM.resolve());g.inventory()
fresh=json.loads((g.OUT/'inventory.json').read_text());inv=json.loads((R/'book/coverage/inventory.json').read_text());assert fresh['counts']==inv['counts']
changes={}
for sec in ['exercises','material_source_units']:
    aa={r['key']:r for r in inv[sec]};bb={r['key']:r for r in fresh[sec]};assert aa.keys()==bb.keys();keys=[]
    for key,row in aa.items():
        nr=bb[key];assert row.keys()==nr.keys()
        assert all(row[f]==nr[f]for f in row if f not in {'source_sha256','source_text','text_sha256'})
        if row['source_text']!=nr['source_text']:keys.append(key)
        else:assert row['text_sha256']==nr['text_sha256']
        if row['source']!=d['current_source53']['file']:assert row==nr
    changes[sec]=keys
assert changes=={'exercises':['verification.html::exercise-17'],'material_source_units':['verification.html::node-1184']}
assert next(r for r in inv['material_source_units']if r['key']==changes['material_source_units'][0])==d['original_entire_material_record']
assert next(r for r in fresh['material_source_units']if r['key']==changes['material_source_units'][0])==d['proposed_entire_material_record']
assert next(r for r in inv['exercises']if r['key']==changes['exercises'][0])==d['original_entire_exercise_record']
assert next(r for r in fresh['exercises']if r['key']==changes['exercises'][0])['source_text']==d['proposed_exercise_text']
selection=json.loads((R/'reports/full-coverage/checkpoint-26-selection.json').read_text());assert len(selection['proof_files'])==1167
for name,row in selection['proof_files'].items():assert H(R/name)==row['sha256']
for name,digest in la['installed26_owner_sha256'].items():assert H(R/name)==digest
assets=json.loads((R/'reports/full-coverage/browser-corrections-26-inputs.json').read_text())['source_sha256'];assert len(assets)==31
for name,digest in assets.items():assert H(R/name)==digest
out=Path('/tmp/modules-conformal-source55-independent-foundations-semantic-and-full29-parser-review-v1.json');assert not out.exists()
evidence={str(P):H(P),str(candidate):H(candidate),str(Path(__file__)):H(__file__),str(primary):H(primary),str(parser):H(parser),old['record']['file']:old['record']['sha256'],lex['record']['file']:lex['record']['sha256'],la['raw_log']:la['raw_log_sha256']}
body={'status':'passed_independent_conformal_source55_precision_semantic_and_full29_parser_review','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'Independent Foundations agent; Modules authored the proposal','proposal':REF(P),'entire_original_proposal_body_and_time':d,'proposal_approved':True,'exact_replacement_decisions':[{'before':x['before'],'after':x['after'],'approved':True,'source_unit_keys':changes['material_source_units'],'reason':'The original exercise already assumes an exchangeable joint score vector. A.s. distinct joint scores supply the exact uniform rank argument. I.i.d. continuous scores are a sufficient example; continuous individual marginals with dependent identical coordinates do not suffice. Independent auxiliary seeds must be used consistently in calibration and test/prediction membership to obtain the randomized exact-rank event and its strict upper bound. The correction changes this shorthand only and leaves the existing joint-law qualification in Section5 and all other clauses intact.','missing_clauses':[]}],'original_full_source_review_body_and_time':old,'full_relevant_primary_D1_D2_text_read':fullprimary,'fresh_full29_parser':{'parser':REF(parser),'inventory':REF(g.OUT/'inventory.json'),'counts':fresh['counts'],'exact_changed_keys':changes,'all_DOM_attrs_keys_locators_lines_reverse_and_other28_pages_exact':True},'current1167_sources31_assets5_owners_checked_exact':True,'whole_d_question_or_exercise_approved':False,'lexicographic_source_body_semantic_approval_inferred':False,'scope':'TMP-only source-precision semantic and exact-byte/full29 parser review. Original7bef body/time retained. No current HTML/inventory/ledger/selected/frozen/PUB write, Source55 protected application, canonical/named compilation or whole(d) proof promotion is inferred. The seed trial actual0 is hash-bound provenance only; its full new bodies require a separate semantic review.','closed_evidence_sha256':evidence}
out.write_text(json.dumps(body,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':'passed','peer':REF(out),'changes':changes}))
