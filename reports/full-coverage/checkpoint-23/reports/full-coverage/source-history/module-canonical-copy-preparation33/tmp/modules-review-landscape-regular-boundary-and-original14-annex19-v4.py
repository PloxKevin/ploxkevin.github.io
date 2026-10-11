from pathlib import Path
import copy, datetime, hashlib, json, re, sys
sys.dont_write_bytecode = True
R = Path('/home/oxrexkevin/SafetyBased')
def P(p): return Path(p) if Path(p).is_absolute() else R / p
def H(p): return hashlib.sha256(P(p).read_bytes()).hexdigest()
old_path = '/tmp/modules-landscape-original14-new-components-annex19-v3.json'
old_hash = '1a368e4899f477984cd71979f7626db3351ebfd91fff9aeb5e957353027fd0c9'
assert H(old_path) == old_hash
A = json.loads(P(old_path).read_text()); pc = A['preservation_check']
I = json.loads(P(A['inventory']).read_text()); S = json.loads(P(pc['selection']).read_text()); F = json.loads(P(pc['frozen_manifest']).read_text())
protected = {}
for p, v in S['proof_files'].items(): protected[p] = v['sha256']; protected.update(v['evidence_sha256'])
frozen = {str(Path(F['snapshot']) / p): h for p, h in F['frozen_inputs_sha256'].items()}
prior = {old_path: old_hash, A['original_review']['file']: A['original_review']['sha256']}
for row in A['all_prior_annex_versions_preserved']: prior[row['file']] = row['sha256']
for row in A['new_independent_precise_component_reviews']:
    prior[row['file']] = row['sha256']; q = json.loads(P(row['file']).read_text()); prior.update(q.get('prior_immutable_artifacts', {}))
for key in ('actual_scope_limited_axiom_evidence_reviews', 'separate_unapplied_readonly_source_proposal_reviews'):
    for row in A[key]: prior[row['file']] = row['sha256']
handoff = '/tmp/modules-landscape-regular-boundary19-handoff-v1.json'
handoff_hash = '5778dfcd6a1470348805b5d34c69da98cf454b6090295f033b6a450eac0a2611'
assert H(handoff) == handoff_hash
J = json.loads(P(handoff).read_text()); strict = J['prior_strict_only_independent_review']
assert strict['sha256'] == '819df24137d463e60ca73ac58f632a5c9df917d2dddc10e039b5f30e2a0cefb0'
prior[handoff] = handoff_hash; prior[strict['file']] = strict['sha256']
def protect():
    assert len(S['proof_files']) == 490 and len(protected) == 565 and len(frozen) == 2431
    assert H(A['source']) == A['source_sha256'] and H(A['inventory']) == A['inventory_sha256']
    assert H(pc['selection']) == pc['selection_sha256'] and H(pc['frozen_manifest']) == pc['frozen_manifest_sha256']
    for rows in (protected, frozen, I['source_sha256'], pc['held_metadata_sha256'], prior, J['proof_source_sha256'], J['preserved_prior_child_sources_sha256']):
        assert all(H(p) == h for p, h in rows.items())
    for row in A['original_review']['all_five_primary_bindings_preserved_exactly']:
        p = row['supplied_local_pdf']; assert H(p['path']) == p['sha256'] and H(p['snapshot']) == p['snapshot_sha256']
        for p in row['supplied_local_texts']: assert H(p['path']) == p['sha256'] and H(p['snapshot']) == p['snapshot_sha256']
        p = row['actual_fresh_pdf_text_extraction']; assert p['exit_code'] == 0 and H(p['output_path']) == p['output_sha256']
protect()
out = Path('/tmp/modules-landscape-regular-boundary-components-review19-v1.json')
ann = Path('/tmp/modules-landscape-original14-new-components-annex19-v4.json')
snap = Path('/tmp/modules-landscape-regular-boundary-independent-read19-v1')
assert not out.exists() and not ann.exists() and not snap.exists(); snap.mkdir()
records = []; failed = []; passes = []
assert len(J['actual_records']) == 10
for row in J['actual_records']:
    rec = row['record']; assert H(rec) == row['record_sha256']
    q = json.loads(P(rec).read_text()); assert q == row['raw_execution_record'] and q['status'] == row['status'] and q['all_sources_still_match']
    a = q['files'][0]; assert a['source_unchanged'] and a['actual_workdir'] == str(R / 'verification/lean') and H(a['log']) == a['log_sha256'] and P(a['log']).read_text() == row['full_actual_log']
    if q['status'] == 'passed':
        assert a['exit_code'] == 0 and H(a['file']) == a['sha256']; passes.append(row)
    else:
        assert a['exit_code'] == 1
        fp = row['failed_source_snapshot']; assert H(fp['path']) == fp['sha256'] == a['sha256']
        failed.append(dict(compiler_manifest=rec, compiler_manifest_sha256=H(rec), raw_execution_record=q,
            failed_source_snapshot=fp['path'], failed_source_snapshot_sha256=H(fp['path']),
            full_failed_source_body_read=True, failed_source_body=P(fp['path']).read_text(), full_raw_log_read=True, actual_raw_log_bytes=row['full_actual_log']))
    records.append(dict(compiler_manifest=rec, compiler_manifest_sha256=H(rec), raw_execution_record=q,
        full_raw_log_read=True, actual_raw_log_bytes=row['full_actual_log']))
assert len(passes) == 6 and len(failed) == 4
evidence = []; all_names = []
for stem, trial, count in [('perturbation', 2, 4), ('local', 2, 2), ('invariance', 3, 4)]:
    rec = 'book/coverage/checks/modules-landscape-regular-boundary-' + stem + '19-trial' + str(trial) + '-standalone.json'
    q = json.loads(P(rec).read_text()); a = q['files'][0]; body = P(a['file']).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', body)
    assert a['actual_command'] == ['lake', 'env', 'lean', str(Path(a['file']).relative_to('verification/lean'))] and not P(a['log']).read_bytes()
    ns = re.search(r'^namespace (\S+)', body, re.M).group(1)
    names = [ns + '.' + n for n in re.findall(r'^theorem\s+(\w+)', body, re.M)]; assert len(names) == count
    all_names += names; copies = {}
    for key, p in dict(source=a['file'], compiler_manifest=rec, raw_log=a['log']).items():
        dst = snap / Path(p).name; dst.write_bytes(P(p).read_bytes()); assert H(dst) == H(p); copies[key] = dict(path=str(dst), sha256=H(dst))
    evidence.append(dict(compiler_manifest=rec, compiler_manifest_sha256=H(rec), actual_exit_code=0, raw_execution_record=q,
        source_body=body, full_source_body_read=True, all_public_theorem_declarations=names, full_raw_log_read=True,
        raw_log_is_empty=True, actual_raw_log_bytes='', exact_read_snapshots=copies))
probe = J['actual_ten_export_axiom_probe']; assert H(probe['record']) == probe['record_sha256'] == '429f40d612498d9a1b7f61fdfc5464bb6e50bb7710e24ababa8c9950b8ad1583'
Q = json.loads(P(probe['record']).read_text()); assert Q == probe['raw_record'] and Q['exit_code'] == 0 and Q['source_unchanged']
assert H(Q['source']) == Q['source_sha256'] and H(Q['log']) == Q['log_sha256'] and Q['proof_source_sha256'] == J['proof_source_sha256']
assert Q['actual_command'] == ['lake', 'env', 'lean', Q['source']] and Q['actual_workdir'] == str(R / 'verification/lean')
assert Q['compiler_toolchain_contents'] == P(Q['compiler_toolchain_file']).read_text() == 'leanprover/lean4:v4.34.1\n'
assert Q['declarations'] == all_names and re.findall(r'^#print axioms (\S+)', P(Q['source']).read_text(), re.M) == all_names
printed = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", P(Q['log']).read_text())
assert len(printed) == 10 and [n for n, _ in printed] == all_names
assert all([v.strip() for v in axioms.split(',')] == ['propext', 'Classical.choice', 'Quot.sound'] for _, axioms in printed)
assert all(Q['actual_printed_axioms'][n] == ['propext', 'Classical.choice', 'Quot.sound'] for n in all_names)
assert Q['full_actual_log'] == P(Q['log']).read_text()
axis = dict(record=probe['record'], record_sha256=H(probe['record']), actual_exit_code=0, full_probe_record=Q,
    full_probe_source_read=True, probe_source_body=P(Q['source']).read_text(), full_actual_log_read=True,
    actual_source_matched_printed_declarations=all_names, precise_scope='These ten declarations only, including four strict perturbation components. Only standard propext/Classical.choice/Quot.sound are actually printed; no unprinted source, aggregate kernel or registry promotion claim.')
for label, p in dict(handoff=handoff, probe_record=probe['record'], probe_source=Q['source'], probe_raw_log=Q['log']).items():
    dst = snap / Path(p).name; dst.write_bytes(P(p).read_bytes()); assert H(dst) == H(p)
apis = []
for p, start, end, desc in [
    ('verification/lean/.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean', 43, 91, 'True Gronwall bound, including K=0, and actual continuity in the additive derivative error. At zero initial distance and zero error its value is exactly zero.'),
    ('verification/lean/.lake/packages/mathlib/Mathlib/Analysis/ODE/Gronwall.lean', 162, 183, 'Actual approximate-trajectory Gronwall proof supplies the distance comparison used between true F and true F+epsilon*v paths on the same positive interval.'),
    ('verification/lean/.lake/packages/mathlib/Mathlib/Topology/Order/IntermediateValue.lean', 314, 339, 'Actual closed-set continuous induction derives full Icc membership from the initial member and arbitrarily nearby later members; csSup membership/nonempty/boundedness are proved internally.'),
    ('verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean', 166, 189, 'Actual strict right-derivative boundary fencing theorem used for perturbed paths. It does not claim weak scalar boundary derivative alone sufficient.')]:
    excerpt = '\n'.join(P(p).read_text().splitlines()[start-1:end]) + '\n'; dst = snap / (Path(p).stem + '-' + str(start) + '-exact-api.txt'); dst.write_text(excerpt)
    apis.append(dict(primary_official_local_source=p, entire_file_sha256=H(p), first_read_line=start, last_read_line=end,
        independently_read_exact_excerpt=excerpt, excerpt_snapshot=str(dst), excerpt_snapshot_sha256=H(dst), assessment=desc))
papers = []
for p, start, end, url, desc in [
    ('sources/text/1609.06408.txt', 200, 215, 'https://arxiv.org/pdf/1609.06408', 'Primary 2017 autonomous-system context takes x in Rn and an ambient locally Lipschitz f; actual maximal unique solution context is used.'),
    ('sources/text/1609.06408.txt', 411, 420, 'https://arxiv.org/pdf/1609.06408', 'Primary 2017 control-affine dynamics are stated for x in Rn with locally Lipschitz f/g.'),
    ('sources/text/1609.06408.txt', 472, 514, 'https://arxiv.org/pdf/1609.06408', 'Primary 2017 definition takes a globally C1 h:Rn->R but calls the barrier condition on D; Corollary2 controller is defined on D; Remark9 distinguishes maximal lifetime from forward completeness.'),
    ('sources/text/1903.11199.txt', 153, 191, 'https://arxiv.org/html/1903.11199v1', 'Primary 2019 context takes f/g locally Lipschitz on a domain D, C1 h:D->R and an actual locally Lipschitz closed-loop with unique maximal solution from every D initial point. It relies on the usual ambient ODE-domain interpretation; these lines do not explicitly say every arbitrary closed D suffices.'),
    ('sources/text/1903.11199.txt', 258, 274, 'https://arxiv.org/html/1903.11199v1', 'Primary 2019 Theorem2/Remark5 explicitly require the nonvanishing gradient at the boundary, identify regular value, and explain the omitted condition in the earlier Nagumo proof.')]:
    excerpt = '\n'.join(P(p).read_text().splitlines()[start-1:end]) + '\n'; dst = snap / (Path(p).stem + '-' + str(start) + '-exact-primary.txt'); dst.write_text(excerpt)
    papers.append(dict(primary_url=url, exact_supplied_local_primary_text=p, text_sha256=H(p), first_read_line=start,
        last_read_line=end, exact_independently_read_excerpt=excerpt, excerpt_snapshot=str(dst), excerpt_snapshot_sha256=H(dst), assessment=desc,
        limit='Exact supplied local primary attribution; no fresh publisher PDF byte identity or whole-paper/concentration approval is asserted.'))
unit = next(u for u in A['exact_original_material_units'] if u['key'] == 'landscape.html::node-1338')
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
localnames = evidence[1]['all_public_theorem_declarations']; invnames = evidence[2]['all_public_theorem_declarations']
z = dict(schema_version=1, kind='independent_exact_regular_boundary_weak_Nagumo_uniform_Picard_perturbation_limit_and_all_forward_invariance_components_review',
    reviewer='/root/modules_resume/gp34_review', reviewed_at_utc=now,
    status='approved_genuine_weak_boundary_only_invariance_on_open_ambient_domain_literal_OR_regular0_nonopen_scope_remains_qualified',
    source=A['source'], source_sha256=A['source_sha256'], inventory=A['inventory'], inventory_sha256=A['inventory_sha256'],
    exact_original_exercise=A['exact_original_exercise'], exact_assigned_material_unit=dict(unit, whole_unit_status='pending_literal_ambient_domain_scope_and_generic_QP_concentration_other_clauses'),
    whole_original_exercise_status='PENDING_not_promoted', actual_standalone_evidence=evidence,
    all_ten_actual_execution_records_rehashed_and_full_logs_read=records, genuine_preserved_failed_executions=failed,
    exact_child_handoff=dict(path=handoff, sha256=handoff_hash, full_handoff_metadata_and_all_ten_records_read=True),
    prior_strict_only_parent_review_preserved=dict(strict, current_new_review_does_not_rewrite_earlier_pending_weak_scope=True),
    actual_ten_export_axiom_evidence=axis, independent_primary_official_local_API_reads=apis,
    precise_primary_ambient_domain_attribution_reads=papers, all_full_read_new_theorem_declarations=all_names,
    precise_mathematical_steps=[
        dict(declarations=evidence[0]['all_public_theorem_declarations'], assessment='The nonzero continuous linear differential yields an actual constant vector with positive directional derivative. C1 continuity preserves positive directional derivative on a true ball inside open D. Boundary weak inwardness plus epsilon times that fixed direction yields true strictly inward F+epsilon*v at zeros there. Actual chain rule and strict scalar fencing derive safety of genuine perturbed paths; no weak invariance is assumed in these four strict components.'),
        dict(declaration=localnames[0], assessment='Constructs eta=r/(L+norm(v)+1)>0, independent of epsilon in (0,1). Actual F norm and Lipschitz bounds imply uniform bounds for F+epsilon*v. Genuine Picard fixed-point construction gives each W starting at x0 and solving the perturbed ODE on one common interval, with ball membership/continuity/actual derivatives derived. W is represented inside the ball for all real times, while ODE/continuity assertions are limited to the certified time interval; no global perturbed solution is claimed.'),
        dict(declaration=localnames[1], assessment='At an actual regular zero, local field Lipschitz behavior and path continuity derive a common ball and positive gamma independent of epsilon. Every genuine perturbed Picard path stays safe by strict fencing. Actual Gronwall bounds dist(x(t),W_epsilon(t)) by gronwallBound(0,K,epsilon*norm(v),t), including K=0. If actual h(x(t)) were negative, continuity gives an open negative neighborhood; actual continuous error bound tends to zero, giving a sufficiently small positive epsilon and a safe W_epsilon(t) in that negative neighborhood, contradiction. No supplied limit path/safety premise or Lipschitz gradient is used.'),
        dict(declaration=invnames[0], assessment='Actual time shift x(t+u) transfers the true right derivative and domain membership to an interval starting at zero; applying the local theorem produces a safe positive future prefix at every regular boundary encounter.'),
        dict(declaration=invnames[1], assessment='The actual set of safe times intersects Icc in a closed set, contains the initial time, and admits safe later members arbitrarily near every safe time: at zero by derived local boundary safety, at positive h by continuity. Genuine closed-set continuous induction derives nonnegativity on the entire existing Icc including endpoint. Initial/path/ODE premises are true existing-path assumptions, not supplied invariance.'),
        dict(declaration=invnames[2], assessment='Every actual ForwardSolution has continuous compact prefixes and true right derivatives derived by strict endpoint neighborhoods. The interval theorem gives safety at each actual forward time and thus derives IsForwardInvariant for ALL true forward solutions from the safe set.'),
        dict(declaration=invnames[3], assessment='Finite-dimensional compact global safe superlevel contained in the open domain plus derived ALL-solution invariance composes the independently reviewed actual Zorn maximal existence/compact continuation chain. It constructs a true global safe path from EVERY safe initial state, including within derivative at zero and ambient derivative for all positive times. Existence, infinite endpoint, invariance or forward completeness are not assumed as desired conclusions.')],
    domain=dict(state='Complete real normed vector space for the uniform Picard/local/weak propagation construction; finite dimension only for the final compact global existence corollary.',
        assumptions='Open ambient D, true locally Lipschitz F on D, C1 h on D, nonzero differential at the relevant zero/all zeros in D, weak nonnegative Lie derivative ONLY at zeros. No C1 field F, Lipschitz gradient, full outside-C barrier inequality, alpha or uniform global Lipschitz bound.',
        forward_solutions='Actual domain-valued ODE paths, with initial state/nonzero endpoint and genuine derivatives; abstract IsForwardInvariant is derived, not assumed.'),
    exact_literal_scope_assessment=dict(unit_key=unit['key'], line=unit['line'], text_sha256=unit['text_sha256'],
        original_OR_excerpt='where either $D$ is an open neighbourhood of $C$ or $0$ is a regular value of $h$',
        original_boundary_excerpt='a check on $\\partial C$ alone, Nagumo\'s condition, needs $\\nabla h\\ne0$ on $\\partial C$',
        approved_component='Genuine generic weak boundary-only regular-zero invariance under an explicit open ambient ODE domain is now closed. It is mathematically distinct from the previously proved open-D/full-domain-barrier inequality theorem.',
        literal_nonopen_branch_status='Pending exact ambient interpretation/extension bridge; not silently approved as merely relative local Lipschitz/C1 data on an arbitrary closed D.',
        assessment='The original OR sentence permits a nonopen barrier-check set D in the regular-value branch. Primary2017 has ambient Rn dynamics and C1 h:Rn->R; primary2019 relies on actual locally Lipschitz closed-loop maximal ODE solutions on its domain. A separate ambient neighborhood or verified extension can reconcile a smaller check set with the new theorem, but this pack does not prove that extension or waive its assumptions. This is an exact formalization/source-scope limitation, not an assertion that the primary regular-boundary theorem is false.',
        minimal_explicit_semantic_qualification='Retain an open ambient neighborhood on which the actual closed-loop is locally Lipschitz and h is C1; distinguish this ODE domain from a possibly smaller set on which only the boundary/barrier inequality is checked. No source change is made by this review.'),
    precise_closed_prior_gap='Weak boundary-only regular-zero invariance and compact safe global existence on a genuine open ambient ODE domain are derived by perturbation, real error bounds and continuous induction, rather than inferred from strict examples or supplied invariance.',
    precise_remaining_clauses=['Original OR regular0 branch needs a precise ambient neighborhood/extension interpretation when D itself is nonopen; the exact open-domain theorem does not prove arbitrary closed-domain relative regularity suffices.',
        'No necessity/converse, arbitrary nonsmooth tangent-cone Nagumo theorem, asymptotic stability, controller existence/regularity, continuous dependence/semigroup flow or learned-policy law follows merely from this pack.',
        'Generic QP regularity, learned residual/ISSf theory, sampled-data safety and actual adaptive bounded-martingale RKHS confidence remain distinct pending components.',
        'Original source rounding/categorical/attribution proposals remain unapplied; whole Exercise1.4/material1338 is not promoted.'],
    warning_precision=['All three actual passing standalone logs are EMPTY.',
        'Perturbation/Local named logs contain real build success output; Invariance named log replays genuine compact-endpoint unused-section and continuation if_true/if_neg deprecation warnings, preserved in full.',
        'All four failed source snapshots and genuine actual error logs are preserved, including failed Local unused-simp warnings. Passing proof bytes were not cleaned or edited by this reviewer.'],
    prior_immutable_artifacts=prior, preservation_check=dict(pc, rechecked_at_utc=now, all_hashes_exact=True),
    limits=['TMP-only independent review during HOLD33; no live source/HTML/assets/inventory/coverage/metadata/selection/frozen/index/ledger/promotion/publication writes.',
        'All ten bodies in three exact actual0 sources independently full-read, plus LocalExistence and GlobalExistence dependencies reread and their earlier exact source reviews preserved. Actual ten-export probe and every pass/fail/named record/rawlog rehashed; no compiler/build/probe newly run by this reviewer.',
        'The ten actually printed axiom declarations have only propext/Classical.choice/Quot.sound. This does not extend an aggregate kernel or unprinted export audit.',
        'Parent strict review819df creation time/body/pending-at-that-time weak decision preserved; original913d/V1/V2/V3 annex histories/19assessments/fiveprimarybindings unchanged. All490/565/2431/29 pages/held metadata exact.'])
assert z['exact_literal_scope_assessment']['original_OR_excerpt'] in unit['source_text'] and z['exact_literal_scope_assessment']['original_boundary_excerpt'] in unit['source_text']
protect(); out.write_text(json.dumps(z, indent=2, ensure_ascii=False) + '\n')
v4 = copy.deepcopy(A); v4['schema_version'] = 4; v4['created_at_utc'] = now
v4['kind'] = 'NEW_v4_precise_component_annex_retaining_original_v1_v2_v3_history_and_adding_actual_weak_regular_boundary_ambient_invariance'
v4['all_prior_annex_versions_preserved'].append(dict(file=old_path, sha256=old_hash, created_at_utc_preserved=A['created_at_utc'], original_status_preserved=A['status'], all_old_component_decisions_times_counts_and_remaining_scopes_unchanged=True))
v4['new_independent_precise_component_reviews'].append(dict(file=str(out), sha256=H(out), reviewed_at_utc=now, status=z['status']))
for e in evidence:
    a = e['raw_execution_record']['files'][0]
    v4['actual_full_read_source_matched_primary_sources'][a['file']] = dict(source_sha256=a['sha256'], compiler_manifest=e['compiler_manifest'],
        compiler_manifest_sha256=e['compiler_manifest_sha256'], actual_execution_record=a, full_body_independently_read_in_review=str(out), public_theorem_count=len(e['all_public_theorem_declarations']), private_lemma_count=0)
v4['new_primary_source_count'] = 24; v4['new_public_theorem_count'] = 95; v4['new_private_lemma_full_body_count'] = 2
v4['fresh_precise_clause_component_updates'].append(dict(original_clause_id='zcbf-domain-and-regularity-routes',
    current_precise_status='NEW_generic_weak_regular_boundary_invariance_on_open_ambient_ODE_domain_closed_original_nonopen_OR_scope_qualified',
    evidence=[str(out)], assessment=z['exact_literal_scope_assessment']['assessment']))
v4['fresh_precise_clause_component_updates'].append(dict(original_clause_id='zcbf-invariance-time-scope',
    current_precise_status='NEW_actual_regular_boundary_only_all_forward_safety_and_compact_global_existence_on_open_ambient_domain_closed',
    evidence=[str(out)], assessment='Actual generic weak boundary-only regular-zero invariance for all ForwardSolution is derived and composed with actual maximal existence/compact continuation. No full outside-C barrier inequality or supplied forward-completeness conclusion. The original smaller/nonopen D branch requires an ambient interpretation or actual extension bridge.'))
for row in v4['current_precise_remaining_clauses']:
    if row['id'] == 'regular_boundary_only_generic_Nagumo_alternative':
        row.update(status='actual_weak_regular_boundary_open_ambient_domain_theorem_closed_literal_nonopen_OR_bridge_pending',
            required='The new generic weak boundary-only theorem is actually proved. Clarify or formally bridge an open ambient locally Lipschitz/C1 ODE neighborhood when the original OR regular0 branch uses a nonopen barrier-check D. No arbitrary closed-D relative-data generalization is inferred.')
v4['actual_scope_limited_axiom_evidence_reviews'].append(dict(file=str(out), sha256=H(out), scope='Embedded actual ten regular-boundary export probe only; exact source/log bindings read.'))
v4['preservation_check'] = dict(pc, rechecked_at_utc=now, all_hashes_exact=True)
v4['limits'] = [s.replace('21 actual primary Lean files / 85 public theorems + 2 private lemmas', '24 actual primary Lean files / 95 public theorems + 2 private lemmas').replace('21principalprintedaxiomdeclarationsacrossactual10+6+5probesonly, not all 85 / aggregate kernel', '31 actually printed principal axiom declarations across actual 10+6+5+10 probes only, not all 95 / aggregate kernel') for s in A['limits']]
v4['limits'].append('NEW V4 closes the exact weak regular-boundary open ambient domain mathematics; it retains the nonopen OR source-scope limitation, all prior history and whole pending status. Parent strict-only review819df and actual10-export probe history remain separate immutable records.')
assert len(v4['actual_full_read_source_matched_primary_sources']) == 24
assert sum(r['public_theorem_count'] for r in v4['actual_full_read_source_matched_primary_sources'].values()) == 95
assert sum(r['private_lemma_count'] for r in v4['actual_full_read_source_matched_primary_sources'].values()) == 2
assert v4['original_review'] == A['original_review'] and v4['whole_original_exercise_status'] == A['whole_original_exercise_status']
protect(); ann.write_text(json.dumps(v4, indent=2, ensure_ascii=False) + '\n'); protect()
for p in (out, ann): print(json.dumps(dict(path=str(p), sha256=H(p)), indent=2))
