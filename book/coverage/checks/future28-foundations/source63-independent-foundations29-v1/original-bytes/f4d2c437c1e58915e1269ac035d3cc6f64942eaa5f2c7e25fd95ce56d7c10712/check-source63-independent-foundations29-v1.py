#!/usr/bin/env python3
import contextlib,hashlib,importlib.util,io,json,sys,tempfile
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/source63-independent-foundations29-v1');OUT.mkdir(exist_ok=True)
REQ=ROOT/'book/coverage/checks/modules-future29/leaky-qc30-and-source63-v1/modules-leaky-qc30-full-scope-independent-review-request29-v1.json'
PROP=Path('/tmp/modules-leaky-convexity-source63-proposal28-v2/modules-leaky-convexity-source63-proposal28-v2.json')
CTX=Path('/tmp/root_tmp_lean_current60_owner28_context_v1.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def resolve(n):return Path(n) if str(n).startswith('/') else ROOT/n
def checkref(r):assert sha(resolve(r['file']))==r['sha256'],r['file'];return resolve(r['file'])
def guards():
 ctx=json.loads(CTX.read_text());assert sha(CTX)=='35ac327b8d62c70dd9e0f83236716ee465d9b188cf656c58be97078b3eea5054'
 for m in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in ctx[m].items():assert sha(ROOT/n)==h,n
 return {'protected_selected_proof_sources':1186,'current_book_assets':31,'live_owners':5,'context':ref(CTX),'inventory_sha256':sha(ROOT/'book/coverage/inventory.json'),'corrections_sha256':sha(ROOT/'book/coverage/material-corrections.json')}
started=datetime.now(timezone.utc).isoformat();before=guards()
assert sha(REQ)=='c61c3f41530e338adadb50f5739771b344f488886fb2700ae83d583cb7545c18'
assert sha(PROP)=='7740f384643979ea5598a66e59d99dbb9e5879a6de75afe4fb546648ca4fed5e'
r=json.loads(REQ.read_text());p=json.loads(PROP.read_text());checkref(p['source']);checkref(p['parser']);candidate=checkref(p['proposed_source']);authorinv=checkref(p['proposed_full29_inventory'])
for n,h in r['required_evidence_artifacts_sha256'].items():assert sha(resolve(n))==h,n
for t in r['actual_six_native_trials_preserved']:
 a=json.loads(checkref(t['actual']).read_text());checkref(t['raw_log']);checkref(t['original_source_snapshot'])
 assert type(a['actual_exit_code']) is int and a['actual_exit_code']==t['actual_lean_exit_code']
 assert a['protection_errors']==[] and a['raw_log_sha256']==t['raw_log']['sha256']
 assert a['source_snapshot_sha256']==t['original_source_snapshot']['sha256']
 assert a['actual_command']==['lake','env','lean',a['source']]
 assert a['actual_workdir']==str(ROOT/'verification/lean')
 assert a['started_at_utc']<a['finished_at_utc'] and a['source_sha256_before']==a['source_sha256_after']==t['original_source_snapshot']['sha256']
assert r['actual_six_native_trials_preserved'][-1]['actual_lean_exit_code']==0
assert p['supporting_lean_draft_compiled'] is False and r['original_source63_author_draft_v4_compiled_false_field_remains_historical'] is True
raw=(ROOT/'SafeLearning/lipsdp.html').read_bytes();new=candidate.read_bytes();repl=p['only_replacement'];b=repl['before'].encode();a=repl['after'].encode()
def exact_patch(old,newer):
 assert old.count(b)==1 and newer.count(a)==1
 assert old.replace(b,a)==newer and newer.replace(a,b)==old
 assert old.count(b'\n')==newer.count(b'\n')
exact_patch(raw,new)
sys.path.insert(0,str(ROOT/'book'))
from validate import Document
old_doc=Document(raw.decode());new_doc=Document(new.decode());assert [(n.tag,n.attrs,n.line) for n in old_doc.nodes]==[(n.tag,n.attrs,n.line) for n in new_doc.nodes]
oldinv=json.loads((ROOT/'book/coverage/inventory.json').read_text())
iso=Path(tempfile.mkdtemp(prefix='source63-fresh-independent29-'));site=iso/'SafeLearning';site.mkdir()
for f in (ROOT/'SafeLearning').glob('*.html'):(site/f.name).write_bytes(new if f.name=='lipsdp.html' else f.read_bytes())
assert len(list(site.glob('*.html')))==29
spec=importlib.util.spec_from_file_location('inventory_source63_fresh_independent',ROOT/'book/inventory_claims.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
mod.ROOT=iso;mod.OUT=iso/'book/coverage'
assert mod.ROOT.resolve().is_relative_to(Path('/tmp')) and mod.OUT.resolve().is_relative_to(iso)
assert mod.ROOT!=ROOT and mod.OUT!=ROOT/'book/coverage'
stream=io.StringIO()
with contextlib.redirect_stdout(stream):mod.inventory()
produced=mod.OUT/'inventory.json';inv=json.loads(produced.read_text());ainv=json.loads(authorinv.read_text())
for d in [inv,ainv]:d.pop('generated_at_utc')
assert inv==ainv
assert inv['counts']==oldinv['counts']==p['counts']
changes={};identity_fields=['key','source','ordinal','locator','anchor','line','label','level','tag','classes','inventory_kind']
for family in ['exercises','material_source_units']:
 old={x['key']:x for x in oldinv[family]};cur={x['key']:x for x in inv[family]};assert set(old)==set(cur)
 changed=[]
 for k,v in old.items():
  q=cur[k]
  assert all(v.get(f)==q.get(f) for f in identity_fields)
  if v['source_text']!=q['source_text'] or v['text_sha256']!=q['text_sha256']:changed.append(k)
  v2={n:z for n,z in v.items() if n!='source_sha256'};q2={n:z for n,z in q.items() if n!='source_sha256'}
  if k not in p['fresh_changed_literal_keys'][family]:assert v2==q2,k
 assert changed==p['fresh_changed_literal_keys'][family]
 changes[family]=changed
for n,h in oldinv['source_sha256'].items():assert inv['source_sha256'][n]==(sha(candidate) if n=='SafeLearning/lipsdp.html' else h)
for k,records in p['entire_current_and_proposed_literal_records'].items():
 fam='exercises' if 'exercise-' in k else 'material_source_units'
 assert next(x for x in oldinv[fam] if x['key']==k)==records['entire_current']
 assert next(x for x in inv[fam] if x['key']==k)==records['entire_proposed']
fixtures=[]
def reject(label,fn):
 try:fn()
 except (AssertionError,KeyError):fixtures.append({'name':label,'rejected':True})
 else:raise AssertionError('accepted bad fixture '+label)
reject('second unapproved prose edit',lambda:exact_patch(raw,new.replace(b'The',b'A',1)))
reject('omitted qualifier edit',lambda:exact_patch(raw,raw))
reject('duplicate qualifier occurrences',lambda:exact_patch(raw,new+a))
reject('wrong reverse bytes',lambda:exact_patch(raw,new.replace(a,a+b' extra')))
reject('HTML node insertion',lambda:exec("assert [(n.tag,n.attrs,n.line) for n in old_doc.nodes]==[(n.tag,n.attrs,n.line) for n in Document(new.decode()+'<p>extra</p>').nodes]"))
reject('wrong declared changed unit',lambda:exec("assert changes['material_source_units']==['lipsdp.html::node-1292']"))
reject('false historical compile retiming',lambda:exec("assert p['supporting_lean_draft_compiled'] is True"))
after=guards();assert before==after
findings={'status':'passed_independent_source63_narrow_wording_and_isolated_full29_parser','reader_started_at_utc':started,'reader_finished_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQ),'proposal':ref(PROP),'fresh_independent_parser_inventory':ref(produced),'fresh_parser_ROOT':str(iso),'fresh_parser_OUT':str(mod.OUT),'fresh_parser_stdout':stream.getvalue(),'changed_keys':changes,'counts':inv['counts'],'all_HTML_tags_attributes_lines_preserved':True,'exact_forward_and_inverse_bytes':True,'full_current_and_proposed_literal_contexts_read':True,'full_unchanged_section6_read':True,'supplemental_passed_v9_witness_and_convex_exception_read':True,'semantic_decision':{'wording_approved':True,'reason':'Matrix concavity is not a universal nonconvex-feasible-set theorem. The full current/proposed literal and unchanged Section6 are consistent after this single qualifier. The actual fixed-positive-multiplier examples show both a nonconvex set at rho=1 and a convex exception at rho=0. This peer approves the narrow phrase and parser mechanics only.','primary_read':{'file':'sources/text/pauli_lcss.txt','sha256':sha(ROOT/'sources/text/pauli_lcss.txt'),'lines':[125,212],'observation':'SectionIII.A equation7 and Remarks3/4 discuss the general convex-training obstruction and alpha=0 conservatism; the source qualifier preserves that obstruction without asserting every specialized positive-alpha instance is nonconvex.'},'source63_applied':False,'whole_exercise12_2_approved':False,'whole_node1293_mathematics_approved':False,'new_Lean_run_by_reviewer':False},'negative_fixtures':fixtures,'fixture_count':len(fixtures),'before':before,'after':after,'protection_errors':[],'coverage_complete':False,'post_freeze_prospective_evidence_not_frozen_in28':True}
(OUT/'findings-v1.json').write_text(json.dumps(findings,indent=2)+'\n')
print(json.dumps({'status':findings['status'],'fresh_parser_counts':inv['counts'],'changed_keys':changes,'fixture_count':len(fixtures),'guards':True}))
