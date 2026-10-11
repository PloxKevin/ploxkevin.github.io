from pathlib import Path
import datetime, hashlib, importlib.util, json, shutil, sys
sys.dont_write_bytecode = True
R = Path('/home/oxrexkevin/SafetyBased')
def P(p): return Path(p) if Path(p).is_absolute() else R/p
def H(p): return hashlib.sha256(P(p).read_bytes()).hexdigest()
proposal='/tmp/modules-landscape-cbf-ambient-domain19-proposal.json'; ph='0a7637735c82a6808f38484ebe60b5883066648000d77fec4c5944ff250e8bb8'
base='/tmp/modules-landscape-regular-boundary-domain-countermodel-components-review19-v1.json'; bh='fab02ca407897db3334f1f6324bb16f8088b4405ad355094c6f9f4e8a3cecde0'
annex='/tmp/modules-landscape-original14-new-components-annex19-v6.json'; ah='85120588ebebbe5176bba4f9b39d2dbdc7a1ec379771de012eb3e67a8a921d16'
assert H(proposal)==ph and H(base)==bh and H(annex)==ah
d=json.loads(P(proposal).read_text()); B=json.loads(P(base).read_text()); A=json.loads(P(annex).read_text()); pc=B['preservation_check']
I=json.loads(P(B['inventory']).read_text()); S=json.loads(P(pc['selection']).read_text()); F=json.loads(P(pc['frozen_manifest']).read_text())
protected={}
for p,v in S['proof_files'].items(): protected[p]=v['sha256']; protected.update(v['evidence_sha256'])
frozen={str(Path(F['snapshot'])/p):h for p,h in F['frozen_inputs_sha256'].items()}
prior={base:bh,annex:ah,**B['prior_immutable_artifacts']}
for k in ('new_independent_precise_component_reviews','actual_scope_limited_axiom_evidence_reviews','separate_unapplied_readonly_source_proposal_reviews'):
    for row in A[k]: prior[row['file']]=row['sha256']
old=P(d['source']).read_bytes(); assert H(d['source'])==d['source_sha256_before']==B['source_sha256'] and H(B['inventory'])==d['inventory_sha256_at_preparation']==B['inventory_sha256']
assert len(d['replacements'])==len(d['precise_subspan_replacements'])==1
r=d['replacements'][0]; s=d['precise_subspan_replacements'][0]
assert r['before'].count(s['before'])==1 and r['before'].replace(s['before'],s['after'],1)==r['after'] and old.count(r['before'].encode())==r['count']==1
assert s['before']=='where either $D$ is an open neighbourhood of $C$ or $0$ is a regular value of $h$'
assert s['after']=='where $D$ is an open ambient neighbourhood of $C$ for the stated locally Lipschitz closed loop; for a boundary-only check, $0$ must additionally be a regular value of $h$'
new=old.replace(r['before'].encode(),r['after'].encode(),1)
assert new.count(r['after'].encode())==1 and new.replace(r['after'].encode(),r['before'].encode(),1)==old
assert old.count(b'\n')==new.count(b'\n') and hashlib.sha256(new).hexdigest()==d['proposed_source_sha256_after']
for k,hk,b in [('source_bytes_before_snapshot','source_bytes_before_snapshot_sha256',old),('source_bytes_proposed_after_snapshot','source_bytes_proposed_after_snapshot_sha256',new)]: assert P(d[k]).read_bytes()==b and H(d[k])==d[hk]
def protect():
    assert len(S['proof_files'])==490 and len(protected)==565 and len(frozen)==2431
    assert H(proposal)==ph and H(B['inventory'])==B['inventory_sha256'] and H(pc['selection'])==pc['selection_sha256'] and H(pc['frozen_manifest'])==pc['frozen_manifest_sha256']
    for rows in (protected,frozen,I['source_sha256'],pc['held_metadata_sha256'],prior,d['actual_proof_source_sha256'],d['preservation_check']['all_live_safelearning_sources_and_assets_sha256']): assert all(H(p)==h for p,h in rows.items())
    assert P(d['source']).read_bytes()==old
    for row in A['original_review']['all_five_primary_bindings_preserved_exactly']:
        q=row['supplied_local_pdf']; assert H(q['path'])==q['sha256'] and H(q['snapshot'])==q['snapshot_sha256']
        for q in row['supplied_local_texts']: assert H(q['path'])==q['sha256'] and H(q['snapshot'])==q['snapshot_sha256']
        q=row['actual_fresh_pdf_text_extraction']; assert q['exit_code']==0 and H(q['output_path'])==q['output_sha256']
protect()
for e in d['actual_standalone_evidence']:
    assert H(e['compiler_manifest'])==e['compiler_manifest_sha256']; q=json.loads(P(e['compiler_manifest']).read_text()); a=q['files'][0]
    assert q['status']=='passed' and q['all_sources_still_match'] and a==e['raw_execution_record'] and a['exit_code']==0 and a['source_unchanged']
    assert H(a['file'])==a['sha256'] and H(a['log'])==a['log_sha256'] and not P(a['log']).read_bytes()
boundary='/tmp/modules-landscape-regular-boundary-components-review19-v1.json'; boundaryhash='304d34278395e386b2c25c3bd0c20e102b75401b0270813a9b479d22d211cac5'
assert H(boundary)==boundaryhash
BR=json.loads(P(boundary).read_text())
declarations=B['all_public_theorem_declarations']
for e in BR['actual_standalone_evidence']: declarations=declarations+e['all_public_theorem_declarations']
assert all(n in declarations for n in d['proof_declarations'])
sys.path.insert(0,str(R/'book'));from validate import Document
BE,AF=Document(old.decode()),Document(new.decode())
assert len(BE.nodes)==len(AF.nodes)==1472 and all((a.tag,a.attrs,a.line)==(b.tag,b.attrs,b.line) for a,b in zip(BE.nodes,AF.nodes))
assert BE.nodes[1337].line==AF.nodes[1337].line==711 and BE.nodes[1337].text()!=AF.nodes[1337].text()
assert BE.nodes[1335].text()==AF.nodes[1335].text() and BE.nodes[1345].text()==AF.nodes[1345].text()
assert len(list(BE.root.descendants('script')))==len(list(AF.root.descendants('script')))
for a,b in zip(BE.root.descendants('script'),AF.root.descendants('script')): assert a.text()==b.text()
sim=Path('/tmp/modules-landscape-cbf-ambient-domain-independent19-v1-simulation')
out=Path('/tmp/modules-landscape-cbf-ambient-domain-independent-proposal-review19-v1.json')
snap=Path('/tmp/modules-landscape-cbf-ambient-domain-independent-read19-v1')
assert not sim.exists() and not out.exists() and not snap.exists(); (sim/'SafeLearning').mkdir(parents=True); snap.mkdir()
for p in (R/'SafeLearning').glob('*.html'): shutil.copyfile(p,sim/'SafeLearning'/p.name)
assert len(list((sim/'SafeLearning').glob('*.html')))==29; (sim/d['source']).write_bytes(new)
spec=importlib.util.spec_from_file_location('landscape_cbf_ambient_domain_independent_inventory19_v1',R/'book/inventory_claims.py')
gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen);gen.ROOT=sim;gen.OUT=sim/'book/coverage'
started=datetime.datetime.now(datetime.timezone.utc).isoformat();gen.inventory();completed=datetime.datetime.now(datetime.timezone.utc).isoformat()
np=gen.OUT/'inventory.json';N=json.loads(np.read_text());assert I['counts']==N['counts']
assert list(I['source_sha256'])==list(N['source_sha256']) and all(N['source_sha256'][p]==(hashlib.sha256(new).hexdigest() if p==d['source'] else h) for p,h in I['source_sha256'].items())
delta={}; details=[]
for section in ('exercises','material_source_units'):
    aa={u['key']:u for u in I[section]};bb={u['key']:u for u in N[section]};assert list(aa)==list(bb);delta[section]=[]
    for key,u in aa.items():
        v=bb[key];assert u.keys()==v.keys()
        for field in u:
            if field not in ('source_sha256','source_text','text_sha256'):assert u[field]==v[field],(key,field)
        if u['source_text']!=v['source_text']:delta[section].append(key);details.append(dict(key=key,line=u['line'],locator=u['locator'],text_sha256_before=u['text_sha256'],text_sha256_proposed_after=v['text_sha256']))
        else:assert u['text_sha256']==v['text_sha256']
        if u['source']!=d['source']:assert u==v
assert delta==d['full_temporary_inventory_parser']['actual_delta']==dict(exercises=['landscape.html::exercise-18'],material_source_units=['landscape.html::node-1338'])
assert details==d['affected_exercises']+d['affected_physical_material_units']
assert H(d['full_temporary_inventory_parser']['simulated_inventory'])==d['full_temporary_inventory_parser']['simulated_inventory_sha256']
assert d['expected_changed_text_keys']==delta['exercises']+delta['material_source_units']
papers=[]
for p,start,end,url,reason in [
    ('sources/text/1609.06408.txt',200,215,'https://arxiv.org/pdf/1609.06408','Actual ambient x in Rn locally Lipschitz field, unique maximal solution interval and every-initial-state forward invariance; not merely relative data on a closed safe set.'),
    ('sources/text/1609.06408.txt',411,420,'https://arxiv.org/pdf/1609.06408','Control-affine f/g locally Lipschitz with ambient x in Rn; primary input constraints context is distinct from relative-domain interpretation.'),
    ('sources/text/1609.06408.txt',472,514,'https://arxiv.org/pdf/1609.06408','Primary globally C1 h, ZCBF on D, feasible feedback and maximal-interval scope; no assertion that this printed corollary explicitly specifies every open-domain hypothesis.'),
    ('sources/text/1903.11199.txt',153,191,'https://arxiv.org/html/1903.11199v1','Actual closed-loop field locally Lipschitz, unique maximal solution and every-initial safety definition. Ordinary ambient ODE interpretation retained; this local text does not literally state D is open in this excerpt.'),
    ('sources/text/1903.11199.txt',258,274,'https://arxiv.org/html/1903.11199v1','The primary Theorem2 and Remark5 explicitly identify regular boundary as needed by Nagumo. Full asymptotic stability claim is not approved by this invariance-only proposal.')]:
    text='\n'.join(P(p).read_text().splitlines()[start-1:end])+'\n';dst=snap/(Path(p).stem+'-'+str(start)+'-'+str(end)+'-ambient-primary.txt');dst.write_text(text)
    papers.append(dict(primary_url=url,exact_supplied_local_primary_text=p,text_sha256=H(p),first_independently_read_line=start,last_independently_read_line=end,exact_independently_read_excerpt=text,excerpt_snapshot=str(dst),excerpt_snapshot_sha256=H(dst),assessment=reason,limit='Exact local primary-attribution contents and all five original paper bindings preserved; no redownload/new publication identity or wholesale primary theorem proof claim.'))
for name,b in [('source-before.html',old),('source-proposed-after.html',new)]: (snap/name).write_bytes(b)
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
z=dict(schema_version=1,status='approved_exact_single_ambient_neighborhood_qualification_readonly_proposal',reviewer='/root/modules_resume/gp34_review',reviewed_at_utc=now,
 proposal=proposal,proposal_sha256=ph,original_preparation_time_preserved=d['prepared_at_utc'],source=d['source'],source_sha256_before=H(d['source']),proposed_source_sha256_after=hashlib.sha256(new).hexdigest(),inventory=B['inventory'],inventory_sha256=B['inventory_sha256'],
 exact_single_paragraph_replacement=d['replacements'],independently_composed_exact_single_subspan_replacement=d['precise_subspan_replacements'],exact_forward_reverse_and_line_counts=True,
 fresh_independent_full_parser=dict(actual_command=['python3','/tmp/modules-review-landscape-cbf-ambient-domain-proposal19-v1.py'],actual_exit_code=0,full_generator_started_at_utc=started,full_generator_completed_at_utc=completed,simulated_inventory=str(np),simulated_inventory_sha256=H(np),page_count=29,counts=N['counts'],actual_delta=delta,all_keys_lines_locators_tags_attributes_order_other_fields_unchanged=True,all_non_target_records_exact=True,all_executable_code_unchanged=True,dom_node_count=len(BE.nodes)),
 exact_original_exercise=A['exact_original_exercise'],exact_original_material_unit=B['exact_assigned_material_unit'],whole_original_exercise_status='PENDING_not_promoted',
 mathematical_and_primary_review=[
 dict(scope='Exact ambient-domain phrase',status='approved_explicit_correct_sufficient_scope_precision',assessment='An open ambient neighborhood for the actual locally Lipschitz closed loop is a genuine sufficient and now fully formalized scope for ODE existence/uniqueness, full-domain nonlinear barrier comparison and boundary-only weak invariance. The added wording makes this explicit rather than letting regular0 substitute for ambient field regularity.'),
 dict(scope='Regular boundary-only alternative',status='approved_with_genuine_extra_regular_value_condition',assessment='For boundary-only checks, regular0 is additionally required. Actual Local2/Invariance4 derive weak invariance using true uniform Picard perturbations/Gronwall/continuous induction and actual all-forward-solution/compact-global construction. The proposal does not impose regular0 on the full open-domain inequality route.'),
 dict(scope='Closed-domain relative-data countermodel',status='approved_genuine_distinct_scope_finding',assessment='Actual h=-x/field=sqrt(max x0)/D=Iic0 gives regular C1 boundary, full on-D alpha=id inequality and relative Lip0 field, yet actual path t²/4 from0 escapes. This disproves safety from merely relative closed-domain data. It does not refute ambient Nagumo, an actual theorem with a locally Lipschitz extension, or a theorem requiring the existing path to remain inD.'),
 dict(scope='Original and primary interpretation',status='explicit_precision_not_a_claim_primary_invalid',assessment='The original ordinary locally Lipschitz condition may already have meant ambient regularity. Primary2017 is globally ambient Rn; primary2019 uses an actual locally Lipschitz closed-loop field/unique maximal interval and explicitly regular boundary. The new phrase aligns the source with precise genuine formal assumptions, without declaring the actual primary theorem false.'),
 dict(scope='Unchanged rest of paragraph',status='not_new_whole_unit_or_exercise_approval',assessment='Cubic degeneracy example, extendedsup/input feasibility, all-initial maximal-time/compact scope, conditional learning filter, certificate/model/ISSf/learned-GP claims remain byte-identical and retain their exact separate component/primary/theory limits. No whole ex18/node1338 approval is supplied.')],
 independent_component_reviews=[dict(file=base,sha256=bh),dict(file=boundary,sha256=boundaryhash),dict(file=annex,sha256=ah)],actual_proof_source_sha256=d['actual_proof_source_sha256'],actual_standalone_evidence=d['actual_standalone_evidence'],exact_actual_declarations=d['proof_declarations'],
 independently_reread_primary_ambient_and_regular_boundary_context=papers,missing_proposed_replacement_clauses=[],
 prior_unapplied_paragraph710_proposal=d['separate_prior_paragraph710_proposal'],prior_unapplied_summary713_proposal=dict(file='/tmp/modules-landscape-guarantee-summary-precision19-proposal.json',sha256='577fed740d13fadafded1fff1ea2c7e4c5e54c4e5e17138dc9b30687e01624c0',independent_review='/tmp/modules-landscape-guarantee-summary-independent-proposal-review19-v1.json',independent_review_sha256='948abef1561f883438c83b89e467ec0090fff018deb456bf9588422bf366bb85'),
 parent_proposal_provenance_wording_note='The separate_prior_paragraph710_proposal limits sentence uses the historical words summary-only. Actual forward/reverse byte checks and fresh parser show this proposal is ONLY paragraph711/node1338; summary713 is unchanged. The historical proposal bytes are retained.',
 prior_reviews_immutable=prior,preservation_check=dict(pc,rechecked_at_utc=now,all_hashes_exact=True,all_live31_source_asset_fingerprints_exact=True),
 limits=['TMP-only HOLD33. No live source/material/assets/inventory/coverage/metadata/index/ledger/selection/frozen/application/wholepromotion/publication writes.',
 'Fresh independent actual full29-page generator completed with556 exercises/12774 physical units: onlyex18/node1338 textdelta, allother record fields/order/keys/lines/locators/DOM1472/executablecode exact.',
 'Exact source-before/proposed-after/forward-reverse, actual three proof-source/compiler/rawlog identities, all490/565/2431/31liveassets/heldmetadata/priorreview/proposal times preserved.',
 'Approved only precise ambient neighborhood and boundary regularity qualification. No unqualified closed-relative-domain safety, generic concentration, all QP regularity/learner law/full ISSf/model-validation or whole material approval.',
 'Original source33 remains unchanged; all three710/711/713 proposals are separate unapplied plans against that original. A fresh serialized identity plan is required after any actual prior source application.'])
protect();out.write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n');protect()
print(json.dumps(dict(path=str(out),sha256=H(out),actual_delta=delta),indent=2))
