from pathlib import Path
import copy, datetime, hashlib, json, re, sys
sys.dont_write_bytecode=True
R=Path('/home/oxrexkevin/SafetyBased')
def P(p):return Path(p) if Path(p).is_absolute() else R/p
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
oldp='/tmp/modules-landscape-original14-new-components-annex19-v6.json';oldh='85120588ebebbe5176bba4f9b39d2dbdc7a1ec379771de012eb3e67a8a921d16'
parent='/tmp/modules-landscape-protected-conditional-noise-components-review19-v1.json';parenth='d59e9fc60819f7141f53af7373d9b1209b8d57e60b85295adc06efecaebacb0b'
ambient='/tmp/modules-landscape-cbf-ambient-domain-independent-proposal-review19-v1.json';ambienth='bef6765a5cda81f333369f7ce529429c13b52ecf399bc0026ec200698a65cc46'
assert H(oldp)==oldh and H(parent)==parenth and H(ambient)==ambienth
A=json.loads(P(oldp).read_text()); D=json.loads(P(parent).read_text()); pc=A['preservation_check']
I=json.loads(P(A['inventory']).read_text());S=json.loads(P(pc['selection']).read_text());F=json.loads(P(pc['frozen_manifest']).read_text())
protected={}
for p,v in S['proof_files'].items():protected[p]=v['sha256'];protected.update(v['evidence_sha256'])
frozen={str(Path(F['snapshot'])/p):h for p,h in F['frozen_inputs_sha256'].items()}
prior={oldp:oldh,parent:parenth,ambient:ambienth,A['original_review']['file']:A['original_review']['sha256']}
for r in A['all_prior_annex_versions_preserved']:prior[r['file']]=r['sha256']
for key in ('new_independent_precise_component_reviews','actual_scope_limited_axiom_evidence_reviews','separate_unapplied_readonly_source_proposal_reviews'):
    for r in A[key]:prior[r['file']]=r['sha256']
def protect():
    assert len(S['proof_files'])==490 and len(protected)==565 and len(frozen)==2431
    assert H(A['source'])==A['source_sha256']==D['source_sha256'] and H(A['inventory'])==A['inventory_sha256']==D['inventory_sha256']
    assert H(pc['selection'])==pc['selection_sha256'] and H(pc['frozen_manifest'])==pc['frozen_manifest_sha256']
    for rows in (protected,frozen,I['source_sha256'],pc['held_metadata_sha256'],prior,D['proof_source_sha256']):assert all(H(p)==h for p,h in rows.items())
    assert H(D['preservation_check']['prior_index'])==D['preservation_check']['prior_index_sha256']
    for row in A['original_review']['all_five_primary_bindings_preserved_exactly']:
        q=row['supplied_local_pdf'];assert H(q['path'])==q['sha256'] and H(q['snapshot'])==q['snapshot_sha256']
        for q in row['supplied_local_texts']:assert H(q['path'])==q['sha256'] and H(q['snapshot'])==q['snapshot_sha256']
        q=row['actual_fresh_pdf_text_extraction'];assert q['exit_code']==0 and H(q['output_path'])==q['output_sha256']
protect()
out=Path('/tmp/modules-landscape-protected-conditional-noise-independent-components-review19-v1.json')
ann=Path('/tmp/modules-landscape-original14-new-components-annex19-v7.json');snap=Path('/tmp/modules-landscape-protected-noise-independent-read19-v1')
assert not out.exists() and not ann.exists() and not snap.exists();snap.mkdir()
evidence=[];names=[];bodies=[]
aggregate='reports/full-coverage/lean-checkpoint-17/verification-original.json';aggregateh='c6bf6eb1bf806d6ee77279903954aa0e1508495fc3a571a049564820ea13133b'
assert H(aggregate)==aggregateh;G=json.loads(P(aggregate).read_text());assert G['status']=='passed'
for row in D['actual_reused_selected_aggregate_kernel_evidence']:
    p=row['source'];assert p in S['proof_files'] and G['proof_sha256'][p]==D['proof_source_sha256'][p]==H(p)
    body=P(p).read_text();ns=re.search(r'^namespace (\S+)',body,re.M).group(1)
    nsnames=[ns+'.'+n for n in re.findall(r'^theorem\s+(\w+)',body,re.M)];names+=nsnames;bodies.append(dict(source=p,source_sha256=H(p),full_actual_source_body=body,all_public_declarations=nsnames))
    clean=re.sub(r'/-[\s\S]*?-/', '',body);clean=re.sub(r'--[^\n]*','',clean);assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean)
    a=row['actual_recorded_kernel_check'];assert any(c==a for c in G['checks']) and a['exit_code']==0 and a['evidence_mode']=='reused_identical_module_and_transitive_local_imports'
    assert row['aggregate_record']==aggregate and row['aggregate_record_sha256']==aggregateh
    assert H(row['retained_raw_log'])==row['raw_log_sha256']==a['log_sha256'] and P(row['retained_raw_log']).read_text()==row['raw_log_text']
    assert H(row['frozen17_duplicate_raw_log'])==row['frozen17_duplicate_sha256']==a['log_sha256'] and P(row['retained_raw_log']).read_bytes()==P(row['frozen17_duplicate_raw_log']).read_bytes()
    original=Path(a['actual_workdir'])/'SafeLearning'/Path(p).name;assert H(original)==H(p)
    reused=a['reused_from'];assert H(reused['report'])==reused['report_sha256']
    for ip,ih in reused['verified_local_import_sha256'].items():
        assert H(ip)==ih and H(Path(a['actual_workdir'])/Path(ip).relative_to('verification/lean'))==ih
    assert reused['original_check']['exit_code']==0 and reused['original_check']['evidence_mode']=='fresh_kernel_replay'
    assert reused['original_check']['log_sha256']==a['log_sha256'] and reused['original_check']['actual_workdir']==a['actual_workdir']
    dst=snap/Path(p).name;dst.write_bytes(P(p).read_bytes());assert H(dst)==H(p)
    evidence.append(dict(row,original_recorded_source_snapshot=str(original),original_recorded_source_snapshot_sha256=H(original),independently_checked_same_module_and_transitive_local_imports=True,source_read_snapshot=str(dst),source_read_snapshot_sha256=H(dst)))
assert len(bodies)==4 and len(names)==17 and names==list(D['selected_export_axiom_dependencies'])
audit=next(c for c in G['checks'] if c['command'][:3]==['lake','env','lean']);assert audit['exit_code']==0
ap=audit['command'][3];ab=P(ap).read_text();lp='reports/full-coverage/lean-checkpoint-17/axioms.log';duplicate='reports/full-coverage/checkpoint-17/reports/lean-verification/axioms.log'
assert P(lp).read_bytes()==P(duplicate).read_bytes();al=P(lp).read_text();allparsed={n:[a.strip() for a in ax.split(',')] for n,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",al)}
selected={n:allparsed[n] for n in names}
assert selected==D['selected_export_axiom_dependencies'] and all(a==['propext','Classical.choice','Quot.sound'] for a in selected.values())
assert all('#print axioms '+n in ab and G['axiom_dependencies'][n]==selected[n] and dict(name=n,file=next(b['source'] for b in bodies if n in b['all_public_declarations'])) in G['declarations'] for n in names)
api=[]
for p,start,end,reason in [
 ('verification/lean/.lake/packages/mathlib/Mathlib/Probability/Moments/SubGaussian.lean',809,858,'Genuine Hoeffding MGF lemma derives the actual parameter from bounded support, zero integral and integrability, including all signs of the MGF argument.'),
 ('verification/lean/.lake/packages/mathlib/Mathlib/Probability/Kernel/CondDistrib.lean',35,91,'The official regular conditional distribution requires Standard Borel only on the real output, constructs true Markov kernel and derives actual composition/joint-law identities.'),
 ('verification/lean/.lake/packages/mathlib/Mathlib/Probability/Kernel/CondDistrib.lean',356,387,'The official conditional expectation equals integral against the actual conditional real law; source uses this for noise mean and exponential moment, not a supplied desired confidence event.')]:
    text='\n'.join(P(p).read_text().splitlines()[start-1:end])+'\n';dst=snap/(Path(p).stem+'-'+str(start)+'-primary-api.txt');dst.write_text(text)
    api.append(dict(primary_official_local_source=p,entire_file_sha256=H(p),first_independently_read_line=start,last_independently_read_line=end,exact_independently_read_excerpt=text,excerpt_snapshot=str(dst),excerpt_snapshot_sha256=H(dst),assessment=reason))
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
z=dict(schema_version=1,kind='independent_exact_protected_four_source_conditional_noise_and_finite_Azuma_component_evidence_supplement',reviewer='/root/modules_resume/gp34_review',reviewed_at_utc=now,
 status='approved_exact_bounded_conditional_MGF_adapted_composition_and_finite_Azuma_components_only',source=A['source'],source_sha256=A['source_sha256'],inventory=A['inventory'],inventory_sha256=A['inventory_sha256'],
 exact_material_unit=D['exact_material_unit'],whole_material_unit_status='PENDING_not_promoted',whole_exercise_status='PENDING_not_promoted',
 parent_precise_review=dict(file=parent,sha256=parenth,reviewer_preserved=D['reviewer'],reviewed_at_utc_preserved=D['reviewed_at_utc'],all_four_assessments_preserved_exactly=D['theorem_groups'],whole_status_remaining_gaps_preserved=D['remaining_gaps']),
 independent_full_read_source_bodies=bodies,all_17_public_declarations=names,actual_reused_selected_kernel_evidence=evidence,actual_new_standalone_evidence=[],
 actual_selected17_axiom_evidence=dict(aggregate_record=aggregate,aggregate_record_sha256=aggregateh,actual_audit_check=audit,exact_audit_source=ap,exact_audit_source_sha256=H(ap),raw_audit_log=lp,raw_audit_log_sha256=H(lp),frozen_duplicate_log=duplicate,frozen_duplicate_log_sha256=H(duplicate),exact_selected17_print_commands=['#print axioms '+n for n in names],independently_parsed_selected17_dependencies=selected,scope='Only these seventeen actual selected public declarations checked in the genuine retained checkpoint17 audit. This is not a fresh audit or a claim about all other printed exports.'),
 independent_primary_official_local_API_reads=api,
 independent_mathematical_assessments=[
 dict(scope='Actual unconditional bounded centered MGF',assessment='The true interval Hoeffding theorem and symmetric specialization derive parameter R² from actual bounded support/zero mean. Independent sample-average/finite tail/calibration statements in Concentration7 are substantive but do not constitute conditional GP confidence.'),
 dict(scope='Actual conditional-past bounded centered MGF',assessment='Standard-Borel ambient ConditionalBounds supplies kernel conditional Hoeffding. Arbitrary-space ConditionalLaw disintegrates the REAL noise, transports support/conditional mean, establishes exponential integrability and the actual conditional expectation bound for every fixed lambda. Azuma kernel formulation makes the all-lambda pointwise version inside the conditional law; no independent-increment assumption is added.'),
 dict(scope='True adapted finite sums',assessment='The past partial sum is measurable at F n because every earlier increment is next-stage strongly measurable and filtration monotone. Actual real conditional-law composition identifies the joint law used to add MGF parameters; induction derives actual parameter nR² for the genuine finite sum.'),
 dict(scope='Actual finite adapted Azuma',assessment='From next-stage measurable, a.e. bounded and actual conditional-zero-mean increments, the actual event {a<=sum_{i<T}Y_i} has probability at most exp(-a²/(2TR²)) for a>0. No independence between increments. T0/R0 totalized real denominator gives exp0=1, a valid vacuous boundary; no fictitious sharp zero-limit formula.'),
 dict(scope='Literal SafeOpt1336 linkage limit',assessment='These are genuine noise components for the stated bounded conditional-zero-mean premise. They do not construct the actual adaptive RKHS/self-normalized posterior confidence event, beta_t=2B+300gamma_t log³(t/delta), all-time simultaneous probability or finite-sample recommendation theorem.')],
 remaining_clauses=D['remaining_gaps'],prior_immutable_artifacts=prior,preservation_check=dict(pc,rechecked_at_utc=now,all_hashes_exact=True),
 limits=['Four protected selected sources/17 actual bodies independently full-read; source identities, reused original module/import source snapshots, all4 real kernel logs/frozen duplicates and exact17 retained audit lists verified.',
 'No new source, compiler run, standalone evidence, kernel replay, selected audit or index mutation. Existing selected17 are separately counted, not added to the27 NEW source/108 public body total.',
 'Parentd59 and original913d/V1–V6/times/decisions remain exact. Generic adaptive RKHS concentration/actual confidence-event probability/all-time posterior/sample-optimality remain pending.',
 'TMP-only HOLD33; source33/INV/all490/565/2431/29 pages/heldmetadata exact, no material/coverage/bodymapping/wholepromotion/application/publication.'])
protect();out.write_text(json.dumps(z,indent=2,ensure_ascii=False)+'\n')
V=copy.deepcopy(A);V['schema_version']=7;V['created_at_utc']=now;V['kind']='NEW_v7_precise_annex_preserving_original_V1_to_V6_and_adding_protected_conditional_noise17_and_ambient_proposal_independent_review'
V['all_prior_annex_versions_preserved'].append(dict(file=oldp,sha256=oldh,created_at_utc_preserved=A['created_at_utc'],original_status_preserved=A['status'],all_old_component_decisions_times_counts_and_remaining_scopes_unchanged=True))
V['new_independent_precise_component_reviews'].append(dict(file=str(out),sha256=H(out),reviewed_at_utc=now,status=z['status'],scope='Protected selected4 sources/17 statements; not new-source totals'))
V['actual_scope_limited_axiom_evidence_reviews'].append(dict(file=str(out),sha256=H(out),scope='Embedded exact existing selected17 audit lists only, reused genuine checkpoint17 evidence'))
V['separate_unapplied_readonly_source_proposal_reviews'].append(dict(file=ambient,sha256=ambienth,scope='Only single ambient-domain1338 phrase independently fresh full-parser reviewed; not applied'))
V['additional_independently_full_read_protected_selected_source_count']=4;V['additional_independently_full_read_protected_selected_public_theorem_count']=17
V['new_source_distinct_printed_principal_axiom_declaration_count']=51;V['additional_actual_selected17_audit_list_count']=17
V['fresh_precise_clause_component_updates'].append(dict(original_clause_id='safeopt-physical-statistical-assumptions',current_precise_status='NEW_protected_actual_bounded_conditional_zero_mean_noise_MGF_and_finite_adapted_Azuma_component_closed_RKHS_confidence_pending',evidence=[parent,str(out)],assessment='The actual noise premise now links to a genuine arbitrary-space conditional MGF and finite adapted-sum tail component; this is not the self-normalized/all-time RKHS posterior confidence event.'))
V['fresh_precise_clause_component_updates'].append(dict(original_clause_id='zcbf-domain-and-regularity-routes',current_precise_status='NEW_explicit_ambient1338_precision_proposal_fresh_independently_approved_unapplied',evidence=[ambient],assessment='Exact single phrase/forward-reverse/fresh full29-page parser approved open ambient closed-loop neighborhood plus additional regular0 only for boundary checks. Actual source33 remains unchanged; no whole1338 promotion.'))
for r in V['current_precise_remaining_clauses']:
    if r['id']=='true_rkhs_conditional_bounded_martingale_adaptive_simultaneous_concentration':r.update(status='true_bounded_conditional_MGF_and_finite_Azuma_component_closed_actual_adaptive_RKHS_confidence_still_pending',required='Actual bounded conditional-zero-mean MGF and finite adapted Azuma are directly proved/read. Still derive the true RKHS/self-normalized adaptive posterior confidence event with literal gamma/beta_t schedule and actual all-time probability, followed by query safety; no desired confidence event supplied as theorem evidence.')
    if r['id']=='regular_boundary_only_generic_Nagumo_alternative':r.update(status='actual_open_ambient_boundary_theorem_closed_single_ambient1338_wording_proposal_fresh_approved_UNAPPLIED',required='The true open ambient weak boundary theorem and relative closed-domain countermodel are read. The explicit ambient source precision proposal has now passed independent exact source-byte/semantic/fresh full29-page parser review. Actual serialized source application/new corrected whole review remain separate; primary ambient theorem is not accused invalid.')
V['previous_V6_limits_preserved_exactly']=A['limits']
V['limits']=['NEW V7 only. Original913d all19 assessments/five papers/time and all V1–V6 bytes/decisions unchanged.',
 'New-source total remains27 files/108 public+3 private bodies, exact51 principal printed declarations. Additional four protected selected sources/17 bodies and17 old selected audit lists are separately bound; no double counting or full aggregate assertion.',
 'Actual bounded conditional MGF and finite adapted Azuma component closed. Generic RKHS/self-normalized/all-time posterior confidence/beta_t/sample-optimality remain pending.',
 'Single ambient1338 wording fresh independently approved but unapplied;710/711/713 proposals separate historical plans against originalsource33. Whole originalex18/node1336/node1338 remain pending.',
 'All490/565/2431/29pages/heldmetadata/proofs/rawlogs/priorreviews/times exact. TMP-only HOLD33, no source/index/coverage/ledger/selection/wholepromotion/application/publication.']
assert V['original_review']==A['original_review'] and V['whole_original_exercise_status']==A['whole_original_exercise_status']
assert V['actual_full_read_source_matched_primary_sources']==A['actual_full_read_source_matched_primary_sources']
protect();ann.write_text(json.dumps(V,indent=2,ensure_ascii=False)+'\n');protect()
for p in (out,ann):print(json.dumps(dict(path=str(p),sha256=H(p)),indent=2))
