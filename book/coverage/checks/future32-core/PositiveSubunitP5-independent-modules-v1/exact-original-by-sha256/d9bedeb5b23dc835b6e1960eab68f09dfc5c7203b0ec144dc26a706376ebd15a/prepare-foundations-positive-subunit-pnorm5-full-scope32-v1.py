from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/future32-foundations/positive-subunit-pnorm5-full-scope-v1';assert not B.exists()
S=Path('/tmp/CompleteFoundationsPositiveSubunitPNorm32-draft-v3.lean');V=R/'book/coverage/inventory-after-correction81.json'
OWN=R/'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1/exact-original-by-sha256/cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a/foundations31-current81-real8-pair-bound-candidate-v2.json'
def path(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(path(n).read_bytes()).hexdigest()
def ref(n):
 p=path(n);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
refs={}
def retain(n):
 p=path(n);r=ref(p)
 assert p.suffix not in ['.pdf'] and not (p.parent.name=='foundations-subunit-p-norm-primary-facts32-v1' and p.suffix=='.txt')
 if p.is_relative_to(R) and '.lake' not in p.parts and not str(p.relative_to(R)).startswith('SafeLearning/'):
  refs[str(p)]=r;return r
 t=B/'exact-original-by-sha256'/r['sha256']/p.name;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert t.read_bytes()==p.read_bytes()
 else:t.write_bytes(p.read_bytes())
 a=ref(t);refs[str(p)]=a;return a
assert sha(S)=='221294e5abbec1d528271aa470d23f38dfdf5b265fbcf52b1200025056035fbe'
assert sha(OWN)=='cce4f603e2d2d1f724290d49cff22becb315b28670b86218a094c92242e1dc5a' and path('book/coverage/foundations.json').read_bytes()==OWN.read_bytes()
assert sha(V)=='b1e914086b3b3ab104bbfff6a647ad5488f6797b2a6f3e4f6aa7ffcb5aa74ef5'
inv=json.loads(V.read_bytes());key='primer-linalg.html::node-171';unit=next(r for r in inv['material_source_units'] if r['key']==key)
owner=json.loads(OWN.read_bytes());rows=[r for r in owner['material_claims'] if key in r.get('source_unit_keys',[])];assert len(rows)==1 and rows[0]['status']=='pending'
sys.path.insert(0,str(R/'book/coverage'));from lean_names import declarations,without_comments
s=S.read_text();names=declarations(s);ts=[r['name'] for r in names if r['kind']=='theorem'];assert len(names)==6 and len(ts)==5 and sum(r['kind']=='def' for r in names)==1
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',without_comments(s))
hist=[]
for role,p in [('original_failed_source_v1','/tmp/foundations-positive-subunit-p-norm5-installed31-trial1.json'),('original_failed_source_v2','/tmp/foundations-positive-subunit-p-norm5-installed31-trial2.json'),('passed_source_v3','/tmp/foundations-positive-subunit-p-norm5-installed31-trial3.json'),('all5_standard_axiom_inspection','/tmp/foundations-positive-subunit-p-norm5-all-public-axioms-installed31-actual-v1.json')]:
 n=json.loads(path(p).read_bytes());assert n['actual_exit_code']==n['actual_runner_exit_code'] and n['protection_errors']==[] and n['source_unchanged'] is True
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert sha(n['source'])==sha(n['source_snapshot'])==n['source_sha256_before']==n['source_sha256_after'] and sha(n['raw_log'])==n['raw_log_sha256']
 hist.append({'history_role':role,'source':retain(n['source']),'native':retain(p),'source_snapshot':retain(n['source_snapshot']),'raw_log':retain(n['raw_log']),'actual_exit_code':n['actual_exit_code'],'actual_emitted_location_first_warning_headers':len(re.findall(r'^[^\n]+:\d+:\d+: warning:',path(n['raw_log']).read_text(),re.M)),'original_body_times':{k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']}})
assert [h['actual_exit_code'] for h in hist]==[1,1,0,0] and hist[2]['source']['sha256']==sha(S) and [h['actual_emitted_location_first_warning_headers'] for h in hist]==[1,6,9,9]
ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",path('/tmp/foundations-positive-subunit-p-norm5-all-public-axioms-installed31-actual-v1.log').read_text(),re.S)
assert [n for n,_ in ax]==ts and all(set(x.strip() for x in v.replace('\n',' ').split(','))<={'propext','Classical.choice','Quot.sound'} for _,v in ax)
providers={n:retain(R/'verification/lean/.lake/packages/mathlib/Mathlib'/n) for n in ['Analysis/SpecialFunctions/Pow/Real.lean','Algebra/Notation/Pi/Basic.lean','Algebra/BigOperators/Group/Finset/Basic.lean','Algebra/BigOperators/Group/Finset/Piecewise.lean','Algebra/BigOperators/Fin.lean']}
full=path('SafeLearning/primer-linalg.html');assert sha(full)==unit['source_sha256']=='eccae82058c393e24f2eaba52dab9021d988562357a2a9bd43934979e0a1113a'
old=full.read_text();before=r'For $p\lt1$ the formula is not a norm:';after=r'In dimensions $n\ge2$, for $0\lt p\lt1$ the formula is not a norm:'
assert old.count(before)==1 and after not in old
new=old.replace(before,after,1);assert new.replace(after,before,1).encode()==full.read_bytes()
B.mkdir(exist_ok=True);P=B/'primer-linalg-positive-subunit-pnorm-prospective-unnumbered32.html';P.write_text(new)
sys.path.insert(0,str(R/'book'));from validate import Document
assert old.count('\n')==new.count('\n') and [(n.tag,n.attrs,n.line) for n in Document(old).nodes]==[(n.tag,n.attrs,n.line) for n in Document(new).nodes]
pros=dict(unit);pros['source_text']=unit['source_text'].replace(before,after,1);assert pros['source_text']!=unit['source_text'];pros['text_sha256']=hashlib.sha256(pros['source_text'].encode()).hexdigest();pros['source_sha256']=sha(P)
facts=path('/tmp/foundations-subunit-p-norm-primary-facts32-v1/foundations-subunit-p-norm-two-primary-norm-facts32-v1.json');assert sha(facts)=='d824f34f4239a90a2f1ac35c6d0b74c047764f83398bde9f86e307fdbf021760'
factsdata=json.loads(facts.read_bytes());assert all(r['actual_http_status']==200 and r['actual_pdftotext']['actual_returncode']==0 for r in factsdata['sources'])
primaryprep=path('/tmp/foundations-subunit-p-norm-primary-facts32-preparation-actual-v1.json');pn=json.loads(primaryprep.read_bytes());assert pn['actual_exit_code']==0 and pn['protection_errors']==[]
body=[]
for m in re.finditer(r'^theorem (\w+)',s,re.M):
 tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|private theorem|def|end |section |namespace )',tail[1:]);b=tail[:stop.start()+1] if stop else tail
 body.append({'declaration':'SafeLearning.CompleteFoundationsPositiveSubunitPNorm32.'+m.group(1),'complete_body_sha256':hashlib.sha256(b.encode()).hexdigest(),'exact_signature':b.split(':=',1)[0].strip()})
heads=lambda text:[m.group(0).split(':=',1)[0] for m in re.finditer(r'(?ms)^theorem .*?:=',text)]
assert heads(s)==heads(path('/tmp/CompleteFoundationsPositiveSubunitPNorm32-draft-v1.lean').read_text())==heads(path('/tmp/CompleteFoundationsPositiveSubunitPNorm32-draft-v2.lean').read_text())
lyap=path('SafeLearning/lyapunov-mpc.html');lines=lyap.read_text().splitlines(keepends=True)
q={'status':'prepared_full_PositiveSubunitPNorm5_source_current171_components_prospective171_whole_independent_mathematical_review_request','errors':[],
 'final_genuine_passed_source':retain(S),'public_theorem_count':5,'public_name_count':6,'definition_count':1,'all_public_declarations':names,'public_theorem_names':ts,'all5_complete_body_signatures':body,
 'entire_current_literal':unit,'exact_planned_prospective_domain_qualified_literal':pros,'actual_installed_owner31_pending_row':rows[0],'immutable_actual_installed_owner31':retain(OWN),'current_inventory81':retain(V),'full_current_Source81_linalg':retain(full),'prospective_full_Source81_page':ref(P),'full_current_norm_context_lines155_190':''.join(old.splitlines(keepends=True)[154:190]),
 'full_actual_used_Mathlib_primary_source_copies':providers,'all_genuine_native_histories':hist,'actual_standard_axioms_per_public_theorem':{n:[x.strip() for x in v.replace('\n',' ').split(',')] for n,v in ax},'all_five_exact_statement_headers_retained_after_two_observed_local_repairs':True,
 'actual_current_installed_owner31_context':retain('/tmp/root_tmp_lean_current81_installed_owner31_context_v1.json'),'actual_current_runner':retain('/tmp/root_tmp_lean_current81_installed_owner31_runner_v1.py'),
 'bounded_two_remote_primary_norm_facts_with_actual_HTTP200_text0_receipts':retain(facts),'bounded_primary_facts_genuine_preparation_native':retain(primaryprep),'bounded_primary_facts_genuine_preparation_raw':retain(pn['log']),'bounded_primary_facts_original_helper':retain('/tmp/prepare-foundations-subunit-p-norm-primary-facts32-v1.py'),'bounded_primary_facts_original_wrapper':retain('/tmp/run-prepare-foundations-subunit-p-norm-primary-facts32-v1.py'),
 'full_remote_PDF_and_complete_text_remain_TMP_offline_excluded_from_Root_packet_and_publication':True,'full_current_Module11_norm_convention_source':retain(lyap),'full_current_Module11_Berkenkamp_context':''.join(lines[60:150]),'full_current_Module11_robustMPC_norm_context':''.join(lines[500:515]),
 'requested_full_mathematical_scope':'Read all5 complete bodies/definition and every used primary proof body, entire current171 plus preceding norm definition and actual Module11 norm convention/citation scopes. Approve only exact components currently true; decide whole exact prospective171 independently, conditional a separately measured narrow parser and eventual application. Retain current171 whole pending for unqualified exponent/dimension domains. No author whole approval, algorithm theorem, whole Module11 or neighboring unit is asserted.',
 'actual_generic_domain':'Every positive subunit exponent 0<p<1 on an arbitrary nontrivial finite coordinate type has a true triangle violation using two distinct coordinate units. This specializes to every finite n>=2; no desired triangle violation is assumed.',
 'actual_printed_fixture':'The actual finite2 power formula gives4 at(1,1) and1 at each coordinate unit for p=1/2, with exact strict2<4.',
 'actual_one_dimensional_countermodel_to_unqualified_non_norm_claim':'For every p>0 on Fin1, the actual formula equals absolute value at every input. Thus positive p<1 alone cannot justify non-norm in all dimensions. No claim for p<=0 is silently inferred.',
 'exact_planned_unnumbered_replacement':{'before':before,'after':after},'citation_domain_notes':factsdata['bounded_factual_assessments'],
 'original_genuine_two_failure_scopes':'Only finite conditional-sum/Pi.single type reductions, the symmetry API for disequalities and normalization of the real base1+1 prevented elaboration. All exact theorem headers remain unchanged; emitted unused-simp warning headers are retained.',
 'current_whole171_approved_by_author':False,'prospective_whole171_approved_by_author':False,'no_Source_ordinal_owner_canonical_selected_or_publication_mutation':True,'coverage_complete':False}
retain(Path(__file__));q['physical_original_leaf_refs']=refs;q['required_evidence_artifacts_sha256']={r['file']:r['sha256'] for r in refs.values()}
O=B/'foundations-positive-subunit-pnorm5-entire-source-current171-components-prospective171-whole-independent-review-request32-v1.json';O.write_text(json.dumps(q,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'request':ref(O),'public_theorems':5,'public_names':6,'source_codes':[h['actual_exit_code'] for h in hist],'physical_refs':len(refs)}))
