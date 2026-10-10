import copy,datetime,hashlib,json,pathlib,re
R=pathlib.Path('/home/oxrexkevin/SafetyBased')
def P(p):
 q=pathlib.Path(p);return q if q.is_absolute() else R/q
def H(p):return hashlib.sha256(P(p).read_bytes()).hexdigest()
ip='book/coverage/inventory-after-correction33.json';assert H(ip)=='c5edf43ad9e1b2d408b328fd331b2a52c624126dd167100541d5ca931986a963'
iv=json.loads(P(ip).read_text());source='SafeLearning/primer-probability.html';assert H(source)==iv['source_sha256'][source]
units=[copy.deepcopy(next(x for x in iv['material_source_units'] if x['key']=='primer-probability.html::node-'+str(n))) for n in [199,200,203,206,207,208]]
ap='reports/full-coverage/lean-checkpoint-18/verification.json';audit=json.loads(P(ap).read_text());assert audit['status']=='passed' and (audit['proof_file_count'],audit['theorem_count'])==(490,5190)
proof={};evidence=[];checks=[];named=[]
selected=['Covariance','Correlation'];supp=['CovarianceMatrix','CovarianceConsequences','GeneralCorrelation']
for n in selected+supp:
 src=f'verification/lean/SafeLearning/CompleteApplied{n}.lean'
 mp=f'book/coverage/checks/applied-next/{n}.json' if n in selected else f'/tmp/applied-future17-actual/{n}.json'
 d=json.loads(P(mp).read_text());assert d['exit_code']==0 and d['sha256_before']==d['sha256_after']==H(src)
 assert H(d['log'])==d['log_sha256'];assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',P(src).read_text())
 proof[src]=H(src);evidence.append(dict(file=src,sha256=H(src),compiler_manifest=mp,compiler_manifest_sha256=H(mp),actual_exit_code=0,raw_log_is_empty=not P(d['log']).read_bytes(),raw_execution_record=d,selection='protected_checkpoint18' if n in selected else 'unselected_supplement_or_import_dependency'))
 if n in selected:
  assert audit['proof_sha256'][src]==H(src)
  ck=copy.deepcopy(next(x for x in audit['checks'] if x.get('module')=='SafeLearning.CompleteApplied'+n));assert ck['exit_code']==0 and H(ck['output_file'])==ck['log_sha256']
  assert H(ck['reused_from']['report'])==ck['reused_from']['report_sha256']
  for p,h in ck['reused_from']['verified_local_import_sha256'].items():assert H(p)==h
  checks.append(ck)
 else:
  np=f'/tmp/applied-{n.lower()}-named-build19.json';nd=json.loads(P(np).read_text())
  assert nd['exit_code']==0 and nd['sha256_before']==nd['sha256_after']==H(src)
  assert H(nd['log'])==nd['log_sha256']
  named.append(dict(manifest=np,manifest_sha256=H(np),actual_execution=nd))
hyp=[
 'Arbitrary probability space and finite real vector dimension; every coordinate has a finite second moment (MemLp2), as explicitly printed. No Gaussianity, finite support, independence or diagonal covariance is inferred.',
 'Correlation uses strictly positive standard deviations sigmaX,sigmaY, with actual variances sigmaX^2,sigmaY^2. Ordinary division is legitimate. The extremal affine statements are almost-sure, not equality at every null-set point.',
 'The selected extremal theorem explicitly gives slope plus/minus sigmaY/sigmaX. The distinct GeneralCorrelation supplement proves the converse for an arbitrary strictly positive/negative affine slope, deriving its forced magnitude from actual affine variance; that is the only additional source-matched correlation scope used here.',
 'Same variance in every direction means every unit Euclidean direction. Selected isotropic_direction_variance proves the stronger sigma^2*sum(v_i^2) formula. Isotropic is a covariance definition and does not mean independent coordinates.',
 'The physical-units sentence is the ordinary dimensional convention: variance has squared units, standard deviation restores the units of the random variable. Actual affine variance scaling and sqrt(.01)=.1 are separately proved.',
 'Positive definiteness/invertibility is proved for the actual covariance matrix via the no-nonzero-almost-sure-constant linear combination condition. Invertibility of a singular covariance or of a zero variance is not inferred.'
]
def ns(n,ds):return ['SafeLearning.CompleteApplied'+n+'.'+d for d in ds]
groups=[
 dict(id='actual-scalar-variance-covariance-standard-deviation-and-affine-scaling',source_clause='Both scalar variance formulas, true centered covariance, standard-deviation convention/noise example and affine variance.',lean_declarations=ns('Correlation',['variance_formulas','standard_deviation_example'])+ns('Covariance',['covariance_matrix_entry']),reason='The selected proof gives the true centered-square integral and second-moment-minus-square formula under L2, exact a^2 affine variance scaling, and sqrt(1/100)=1/10. Covariance is the actual centered cross integral. Units are separately identified as dimensional convention, not a theorem about physical measurement systems.'),
 dict(id='actual-finite-vector-outer-covariance-and-affine-transformation',source_clause='Whole203 matrix formula, coordinate entries and Cov(AX+b)=A Sigma A^T.',lean_declarations=ns('Covariance',['covariance_matrix_entry','affine_covariance_transform']),reason='Entrywise actual centered cross integrals are precisely the expected outer matrix; finite sums and coordinate L2 give the true rectangular affine transformation formula. Translation cancels in the covariance, with no missing matrix shape premise.'),
 dict(id='actual-isotropic-coordinate-and-all-unit-direction-variance',source_clause='Isotropic Sigma=sigma^2 I, equal coordinate variance/uncorrelatedness and every unit-direction variance.',lean_declarations=ns('Correlation',['covariance_isotropic_entries','isotropic_direction_variance']),reason='The selected exact iff identifies equal diagonal variances and zero off-diagonal covariances. Its arbitrary-vector formula gives sigma^2 for every Euclidean unit direction. No independent/noise-distribution claim is implied.'),
 dict(id='actual-standardized-correlation-unit-interval-and-pair-matrix',source_clause='Covariance of standardized variables, variances2(1 plus/minus rho), rho in[-1,1], and literal pair matrix.',lean_declarations=ns('Correlation',['covariance_standardized','correlation_variance_identity','correlation_interval','covariance_pair_matrix']),reason='The selected signed difference variance theorem covers both source standardized sum/difference by s=plus/minus1 and variance symmetry. Actual nonnegativity proves the interval; positive sigma factors reconstruct the exact off-diagonal rho*sigmaX*sigmaY entries.'),
 dict(id='actual-both-extremal-correlation-affine-iff-with-arbitrary-signed-slope',source_clause='rho=plus/minus1 iff Y is almost surely affine in X with the corresponding slope sign.',lean_declarations=ns('Correlation',['correlation_extreme_iff_affine'])+ns('GeneralCorrelation',['actual_affine_almost_sure_relation_gives_covariance_and_variance','actual_correlation_one_iff_a_positive_slope_almost_sure_affine_relation','actual_correlation_negative_one_iff_a_negative_slope_almost_sure_affine_relation']),reason='The selected theorem proves the full normalized-slope alternative. The distinct supplement additionally accepts any strictly signed affine slope and derives a*sigmaX=plus/minus sigmaY internally from its variance; it therefore proves the exact general iff wording without silently imposing the normalized slope as an extra premise.'),
 dict(id='actual-covariance-centered-quadratic-PSD-and-PD-invertibility-iff',source_clause='Whole206/207/208 centered-square quadratic identity, true PSD and PD/invertibility iff no nonzero combination is almost surely constant.',lean_declarations=ns('Covariance',['covariance_quadratic_is_variance','covariance_matrix_posSemidef','variance_zero_iff_constant','covariance_posDef_iff_no_constant_combination','covariance_invertible_of_no_constant_combination'])+ns('Correlation',['covariance_quadratic_centered_outer_products','covariance_matrix_invertible_iff']),reason='The selected all-vector identities equate the actual quadratic form with the centered square integral and the true variance. Hermitian symmetry and variance nonnegativity give official Matrix.PosSemidef. Variance0 iff almost-sure constant yields the precise PD condition and official IsUnit/invertibility iff. The heading207 asserts PSD and is itself mapped to this proof, not classified as a nominal label.')]
for g in groups:
 g.update(status='approved_precise_component',review_status='approved_precise_source_component',per_clause_reason=g.pop('reason'),hypotheses=hyp,missing_clauses=[])
 for d in g['lean_declarations']:
  stem,short=d.rsplit('.',1);src='verification/lean/'+stem.replace('.','/')+'.lean'
  assert src in proof and re.search(r'\b(?:theorem|lemma)\s+'+re.escape(short)+r'\b',P(src).read_text())
  if src.endswith(('CompleteAppliedCovariance.lean','CompleteAppliedCorrelation.lean')):
   assert any(x['name']==d and x['file']==src for x in audit['declarations'])
   assert set(audit['axiom_dependencies'][d])<=set(audit['allowed_standard_axioms'])
for u in units:
 n=int(u['key'].split('-')[-1])
 u.update(review_status='approved_complete_source',hypotheses=hyp,missing_clauses=[])
 if n==200:u.update(status='not_formalizable',per_unit_reason='This literal names the definitions variance, covariance and covariance matrix; it asserts no formula or theorem. Its mathematical definition body is separately proved, not inferred from this label.')
 else:u.update(status='proved',per_unit_reason='Every actual literal formula/assertion is covered by the exact selected covariance/correlation groups and the precise arbitrary-signed-affine converse supplement. Heading207 contains a PSD assertion and receives proved status.')
mp='reports/full-coverage/checkpoint-18-manifest.json';m=json.loads(P(mp).read_text());paths={}
for p,row in m['proof_files'].items():
 assert H(p)==row['sha256'];paths[p]=row['sha256']
 for ep,h in row['evidence_sha256'].items():assert H(ep)==h;paths[ep]=h
for p,h in m['frozen_inputs_sha256'].items():assert H(R/m['snapshot']/p)==h
pd=json.loads(P('/tmp/foundations-future19-held-work-index-v18.json').read_text())
for p,h in pd['held_current_metadata_sha256'].items():assert H(p)==h
out=dict(schema_version=1,status='independent_full_source_review_passed',reviewer='/root/foundations_next',reviewed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_sha256={source:H(source)},inventory=ip,inventory_sha256=H(ip),proof_source_sha256=proof,actual_standalone_evidence=evidence,actual_named_evidence=named,
 actual_checkpoint18_reused_kernel_evidence=dict(report=ap,report_sha256=H(ap),status='passed',proof_file_count=490,theorem_count=5190,actual_module_checks=checks,limits='Selected proofs use passed actual18 reused identical source/import kernel evidence. New supplement has genuine standalone/named0 but is unselected and is not claimed to have a new aggregate audit.'),
 records=[],reviewed_clauses=groups,material_units=units,missing_clauses=[],
 explicit_baseline_overlap=dict(protected_baseline_sources={p:h for p,h in proof.items() if p.endswith(('CompleteAppliedCovariance.lean','CompleteAppliedCorrelation.lean'))},new_scope='Only the GeneralCorrelation arbitrary strictly signed affine-slope converse is used as a new direct source wrapper.',overlapping_sources=['verification/lean/SafeLearning/CompleteAppliedCovarianceMatrix.lean','verification/lean/SafeLearning/CompleteAppliedCovarianceConsequences.lean'],reason='Matrix and Consequences are genuine import dependencies of the supplement. Their PSD/affine/centered-square/isotropy/standard-deviation results already have selected source correspondence and are not counted as newly uncovered mathematics.'),
 preserved_overwrite_history=dict(report='/tmp/applied-selected-correlation-overwrite-restoration19.json',report_sha256=H('/tmp/applied-selected-correlation-overwrite-restoration19.json'),selected_restoration_named='/tmp/applied-selected-correlation-restoration-named19.json',selected_restoration_named_sha256=H('/tmp/applied-selected-correlation-restoration-named19.json'),reason='The selected old Correlation source is restored80df40 and was freshly rehashed here. Wrong-name new records are historical only; this review uses the distinct GeneralCorrelation filename/namespace actual0.'),
 preservation_check=dict(manifest=mp,manifest_sha256=H(mp),selected_proofs_checked=len(m['proof_files']),unique_selected_source_evidence_paths_checked=len(paths),frozen_inputs_checked=len(m['frozen_inputs_sha256']),all_exact=True),
 limits=['Full six exact literals and all five full mathematical sources were independently read. Units199/203/206/207/208 proved; nominal200 individually classified. No ensemble211 or independence221 claim is inferred.', 'Selected Covariance/Correlation canonical raw logs are empty. New Matrix, Consequences and GeneralCorrelation raw logs retain actual harmless warnings. All source/compiler/named/raw-log hashes were independently checked.', 'TMP only under unreleased HOLD33; no live mapping, source, inventory, builder, ledger or offer write.'])
q=P('/tmp/probability-covariance-material-full-source-review19-v1.json');assert not q.exists();q.write_text(json.dumps(out,indent=2)+'\n');print(q,H(q),'5proved/1nominal literals approved')
