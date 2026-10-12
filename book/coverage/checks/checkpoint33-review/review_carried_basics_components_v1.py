from pathlib import Path
import json
import hashlib

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = Path(__file__).resolve().parent
OWNER = ROOT / 'book/coverage/foundations.json'
REVIEW = OUT / 'independent-six-qualifier-cumulative-review-v1.json'


def ref(path):
    data = path.read_bytes()
    return {'file': str(path.relative_to(ROOT)), 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


owner = json.loads(OWNER.read_bytes())
review = json.loads(REVIEW.read_bytes())
records = {m['key']: m['entire_candidate_literal'] for m in review['whole_statement_mappings_conditional_on_exact_application_and_canonical_audit']}
records[review['node922']['entire_candidate_literal']['key']] = review['node922']['entire_candidate_literal']
assessments = {
    1: 'The geometric recurrence and every-prefix envelope are unchanged. The explicit nonnegative error convention narrows the prose; the original q>=0 envelope result remains valid.',
    2: 'The newly explicit nonnegative error convention matches the existing nonnegative hypotheses and 0<=q<1 convergence result.',
    3: 'The new positive-C qualifier matches the existing quadratic-recursion hypotheses. The small-initial-error condition remains required only for convergence, as retained in the original row.',
    4: 'The exact positive reciprocal-power example now removes the ambiguous upper-bound classification. The existing positive-power asymptotics and no-geometric-BigO component retain their precise scope.',
    5: 'The concrete scalar f(x)=x^2-1 fixture is C2 with regular root1 and invariant [.5,1.5] neighborhood. It remains a valid concrete instance of the explicitly qualified Newton example.',
    6: 'The actual regular-Newton iterate neighborhood, envelope and convergence statements retain their concrete sufficient initial domain.',
    7: 'The singular f(x)=x^2 orbit remains an explicit boundary countermodel. The new regular-root qualifier excludes it from the generic Newton statement; retain this row as the original reviewed boundary component, not as a regular-root instance.'}
cutoff_assessments = {
    1: 'The new prose explicitly distinguishes the exact geometric envelope iff from sufficiency for faster bounded errors, matching the existing positive quotient/log hypotheses.',
    2: 'The exact half-rate envelope first crossing at20 is unchanged and explicitly identified as an envelope crossing.',
    3: 'The exact reciprocal-square-root cutoff iff is unchanged, with positive index and tolerance retained; the printed natural-index k>=1 domain is narrower.',
    4: 'The exact natural-index square-root crossing at10^12 is unchanged and retains positive-index hypothesis.'}
rows = []
for index in [*range(350, 357), *range(359, 366), *range(367, 371)]:
    row = owner['material_claims'][index]
    assert row['status'] == 'proved'
    assert len(row['source_unit_keys']) == 1
    key = row['source_unit_keys'][0]
    assert key in records
    suffix = int(row['id'].rsplit('-', 1)[1])
    explanation = cutoff_assessments[suffix] if key.endswith('node-922') else assessments[suffix]
    new = dict(row)
    record = records[key]
    for field, inventory_field in [('source_text', 'source_text'), ('source_text_sha256', 'text_sha256'), ('source_sha256', 'source_sha256')]:
        new[field] = record[inventory_field]
    assert {k: v for k, v in row.items() if k not in ('source_text', 'source_text_sha256', 'source_sha256')} == {k: v for k, v in new.items() if k not in ('source_text', 'source_text_sha256', 'source_sha256')}
    inverse = dict(new)
    for field in ('source_text', 'source_text_sha256', 'source_sha256'):
        inverse[field] = row[field]
    assert inverse == row
    rows.append({'foundation_material_claim_index': index, 'claim_id': row['id'],
                 'original_row': row, 'candidate_row': new,
                 'decision': 'approved_existing_component_correspondence_rebase_only',
                 'reason': explanation, 'exact_inverse': True,
                 'statements_hypotheses_declarations_status_and_original_correspondence_unchanged': True})
assert len(rows) == 18
assert sum('node-916' in r['claim_id'] for r in rows) == 7
assert sum('node-918' in r['claim_id'] for r in rows) == 7
assert sum('node-922' in r['claim_id'] for r in rows) == 4
report = {'status': 'approved_independent_18_existing_Basics_components_literal_identity_rebase',
          'errors': [], 'original_foundation_owner': ref(OWNER), 'cumulative_source_review': ref(REVIEW),
          'components': rows, 'unchanged_original_scope_authority': 'Each original correspondence and hypothesis string is retained exactly in original_row and candidate_row.',
          'semantic_decision': 'All18 original component propositions remain valid against the exact cumulative qualification; no stronger algorithm, first-index necessity for arbitrary errors, unqualified Newton or polynomial-upper-bound classification is inferred.',
          'node922_whole_still_pending': True, 'new_theorem_or_component_count': 0,
          'current_owner_mutated': False, 'coverage_complete': False}
path = OUT / 'independent-18-carried-basics-component-rebase-v1.json'
assert not path.exists()
path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
print(json.dumps(ref(path)))
