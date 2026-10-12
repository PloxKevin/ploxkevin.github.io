from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, copy
R=Path('/home/oxrexkevin/SafetyBased')
Q=R/'book/coverage/checks/future28-foundations/basics-bibliography8-primary-classification-v1/foundations-basics-bibliography8-full-literal-classification-request28-v1.json'
O=Path('/tmp/foundations-bibliography8-independent-modules28-peer-original-v1.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not O.exists()
assert sha(Q)=='8d16c44ad2d24b4f328b42c8f96001dc21674988573d4e737c3369969bc86480'
q=json.loads(Q.read_bytes()); start=datetime.now(timezone.utc).isoformat()
refs=dict(q['required_evidence_artifacts_sha256'])
for n,h in refs.items():
 p=R/n; assert not Path(n).is_absolute() and '..' not in Path(n).parts and p.resolve().is_relative_to(R) and sha(p)==h,n
for k in ['actual_author_preparation','actual_author_raw_log','original_closed_byte_alias_catalog','own_primary_factual_observations','original_author_request','original_source','original_owner','current_inventory','original_guard_context']:
 v=q[k];p=Path(v['file']);p=p if p.is_absolute() else R/p;assert sha(p)==v['sha256'],k
source=Path(q['original_source']['file']);owner=Path(q['original_owner']['file'])
assert source.read_bytes()==(R/'SafeLearning/primer-basics.html').read_bytes()
assert owner.read_bytes()==(R/'book/coverage/foundations.json').read_bytes()
base=json.loads(owner.read_bytes()); inv=json.loads(Path(q['current_inventory']['file']).read_bytes())
bykey={r['key']:r for r in inv['material_source_units']}
context='\n'.join(source.read_text().splitlines()[1674:1698]); assert context==q['source_context']['text']
assert hashlib.sha256(context.encode()).hexdigest()==q['source_context']['sha256']
keys=[f'primer-basics.html::node-{n}' for n in range(1648,1691,6)]
assert [r['source_unit_key'] for r in q['rows']]==keys
def valid(row):
 old,new=row['original_row'],row['proposed_row'];key=row['source_unit_key'];unit=bykey[key]
 assert old in base['material_claims'] and sum(c['id']==old['id'] for c in base['material_claims'])==1
 assert old['source_unit_keys']==[key] and old['source_text']==unit['source_text']
 assert old['source_text_sha256']==unit['text_sha256'] and old['source_sha256']==unit['source_sha256']
 assert old['status']=='pending' and old['lean_declarations']==[]
 for k in ['id','source_unit_keys','source','source_sha256','locator','source_text','source_text_sha256','lean_declarations']:assert old[k]==new[k],k
 assert new['status']=='not_a_formal_claim' and new['hypotheses']==[] and new['remaining_gaps']==[]
 assert new['kind']=='individually_reviewed_bibliographic_and_curricular_reference'
 assert new['statement_in_prose']==old['source_text']
 assert row['new_math_proof_or_external_whole_book_approval'] is False
 facts=row['primary_factual_observation'];assert facts['facts'] in new['correspondence'] and facts['qualification'] in new['correspondence']
 assert all(u.startswith(('http://','https://')) for u in facts['primary_urls'])
for row in q['rows']:valid(row)
edited=copy.deepcopy(base); affected=[]
for row in q['rows']:
 i=edited['material_claims'].index(row['original_row']);affected.append(i);edited['material_claims'][i]=copy.deepcopy(row['proposed_row'])
assert edited['exercises']==base['exercises'] and edited['proof_files']==base['proof_files']
counts={s:sum(r['status']==s for r in edited['material_claims']) for s in ['proved','pending','not_a_formal_claim']}
assert counts==q['proposed_local_count_preview_if_independently_approved']
assert counts['proved']==sum(r['status']=='proved' for r in base['material_claims'])
for i,row in zip(affected,q['rows']):edited['material_claims'][i]=copy.deepcopy(row['original_row'])
assert edited==base
receipts=[]
for v in q['original_http_receipts']:
 p=R/v['file'];assert sha(p)==v['sha256'];d=json.loads(p.read_bytes());assert d['protection_errors']==[] and d['protected_before']==d['protected_after'];receipts.extend(d['results'])
assert len({r['id'] for r in receipts})==len(receipts)
ids={r['id']:r for r in receipts}
assert ids['sutton-current-full-http']['bytes']==73129769
assert any(r.get('error') for r in receipts)
assert ids['abbott']['bytes']==3038 and ids['abbott']['http_status']==200
assert q['historical_http_guard_scope'].startswith('1186 selected sources,29 HTML inputs,five owners')
assert q['current_author_guard_scope']=={'installed_owners':5,'selected_sources':1186,'source_browser_assets':31}
assert q['inventory_units_dropped']==0 and q['new_lean_declarations']==[]
assert q['live_ledger_or_candidate_or_html_or_git_writer_executed'] is False and q['lean_compilation_or_math_whole_approval_claimed'] is False
# Entire original downloaded texts are read only offline; no book bytes enter this evidence packet.
for n,h in q['offline_remote_originals_sha256'].items(): assert sha(Path(n))==h,n
mit=Path('/tmp/foundations-basics-eight-primary-bibliography28-v1/mit-pdf.txt').read_text()
lebl=Path('/tmp/foundations-basics-eight-primary-bibliography28-v1/lebl-pdf.txt').read_text()
arora=Path('/tmp/foundations-basics-primary-chapter-checks28-v1/arora-full-http.txt').read_text()
boyd=Path('/tmp/foundations-basics-eight-primary-bibliography28-v1/boyd-pdf.txt').read_text()
sutton=Path('/tmp/foundations-basics-primary-chapter-checks28-v1/sutton-current-full-http.txt').read_text()
assert 'The Invariant Principle' in mit and 'start state' in mit[283550:286000] and 'base case' in mit[283550:286000]
assert 'Theorem 7.6.2' in lebl and 'nonempty complete metric space' in lebl[877185:878200]
assert 'January 2007' in arora[:800] and 'In the previous chapter we' in arora[157013:159900]
assert all(t in boyd for t in ['First published 2004','A.2.1   Open and closed sets','A.2.2   Supremum and infimum'])
assert '© 2018, 2020' in sutton[:2500] and '4.4      Value Iteration' in sutton and '3.3         Returns and Episodes' in sutton
tests=[]
def reject(label,mutate):
 row=copy.deepcopy(q['rows'][0]);mutate(row)
 try:valid(row)
 except (AssertionError,KeyError):tests.append(label);return
 raise AssertionError('fixture accepted:'+label)
reject('changed full literal',lambda r:r['proposed_row'].__setitem__('source_text','replacement'))
reject('theorem promotion',lambda r:r['proposed_row'].__setitem__('status','proved'))
reject('invented declaration',lambda r:r['proposed_row'].__setitem__('lean_declarations',['fake']))
reject('changed identity',lambda r:r['proposed_row'].__setitem__('id','wrong'))
reject('dropped original unit',lambda r:r['proposed_row'].__setitem__('source_unit_keys',[]))
reject('external whole book approval',lambda r:r.__setitem__('new_math_proof_or_external_whole_book_approval',True))
reject('lost scope qualification',lambda r:r['proposed_row'].__setitem__('correspondence',r['primary_factual_observation']['facts']))
facts=[
 ('1648','Third edition and 2018 copyright, free author PDF, and the listed proof topics match the author page. The superlative reading advice is a curricular preference.','https://richardhammack.github.io/BookOfProof/'),
 ('1654','The publisher identifies the 2019 third edition. Its indexed third-edition preface places quantifiers in chapter 2, structured proof methods in 3, and induction in 6. Proof structure follows logical form as pedagogical guidance.','https://assets.cambridge.org/97811084/24189/frontmatter/9781108424189_frontmatter.pdf'),
 ('1660','The 2015 MIT book directly explains induction over execution length, with both a start-state obligation and transition preservation. The bibliography describes that method; it does not waive those conditions.','https://ocw.mit.edu/courses/6-042j-mathematics-for-computer-science-spring-2015/resources/mit6_042js15_textbook/'),
 ('1666','Springer confirms edition 2, 2015, and the analysis topics. The actual twelve-page frontmatter confirms compactness and continuity content; native 3038-byte HTTP200 challenge bodies remain explicitly unusable. Readability is a subjective recommendation.','https://link.springer.com/book/10.1007/978-1-4939-2712-8'),
 ('1672','The author confirms version 6.3 dated May 15, 2026. Offline section 7.6 includes the full contraction fixed-point proof on a nonempty complete metric space. The row attributes that proof to the book rather than adding an unqualified local theorem.','https://www.jirka.org/ra/'),
 ('1678','The author-hosted book first appeared in 2004. Appendix A directly covers norms, open and closed sets, and suprema and infima. Accessible PDF reading retains the publisher copyright.','https://web.stanford.edu/~boyd/cvxbook/'),
 ('1684','Cambridge dates the print edition 2009 and chapter 2 concerns NP-completeness. The exact offline author draft is January 2007; chapter 2 references P from chapter 1 and supplies reductions. No edition dates are conflated.','https://www.cambridge.org/core/books/abs/computational-complexity/np-and-np-completeness/D1D3CDF090A9D3451ACD092A307050C8'),
 ('1690','MIT Press confirms the 2018 second edition and open author access. The exact offline PDF is a 2020 revision of that edition, with discounted returns in 3.3 and value iteration in 4.4. No arbitrary value-iteration convergence is asserted.','https://mitpress.mit.edu/9780262039246/reinforcement-learning/')]
decisions=[{'source_unit_key':f'primer-basics.html::node-{n}','approved_exact_nonformal_bibliographic_classification':True,'missing_clauses':[],'independent_factual_and_scope_reason':s,'primary_url':u} for n,s,u in facts]
out={'status':'passed_independent_full_eight_bibliographic_literal_factual_and_nonformal_classification_review','errors':[],'reviewer':'/root/modules_finish28','request':{'file':str(Q.relative_to(R)),'sha256':sha(Q)},'reader_started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'individual_full_literal_decisions':decisions,'all_eight_exact_original_and_proposed_rows_read':True,'all_22_durable_original_bytes_checked':True,'original_primary_endpoint_failures_and_dummy_bodies_retained':True,'own_new_web_failures':['Princeton author page 403 in web tool','Sutton author page 502 in web tool','Cambridge frontmatter direct timeout; indexed primary preface read','Springer direct colon-PDF URL inaccessible; publisher PDF link succeeded'],'own_primary_web_checks':['Hammack author page','Cambridge book page and indexed third-edition preface','MIT OCW resource','Springer book page and actual 12-page frontmatter','Lebl author page','Boyd author page','Cambridge chapter2 page','MIT Press book page'],'offline_chapter_scope_read':['MIT5.4.3 full invariant explanation including base and step','Lebl7.6.1 full theorem7.6.2 and proof','Boyd AppendixA referenced section bodies','Arora January2007 title and chapter2 introduction/NP definition','Sutton2018/2020 title, full3.3 discounted return and full4.4 value iteration explanation'],'remote_originals_remain_TMP_offline_only':True,'forward_and_inverse_eight_proposals_exact':True,'isolated_count_preview':counts,'new_mathematical_proof_or_exercise_or_external_whole_book_approval':False,'no_other_pending_mathematical_topics_reclassified':True,'live_html_owner_selection_or_publication_changes':False,'coverage_complete':False,'negative_fixtures':tests}
O.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'peer':str(O),'sha256':sha(O),'eight_decisions':len(decisions),'negative_fixtures':len(tests)}))
