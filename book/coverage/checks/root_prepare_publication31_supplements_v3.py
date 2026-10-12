"""Build an explicit, bounded map of reviewed checkpoint31 publication evidence."""
from pathlib import Path
import argparse, hashlib, json, re, shutil

ROOT = Path(__file__).resolve().parents[3]
PUB = ROOT/'reports/book/publication-repo'
OUT = ROOT/'reports/full-coverage/publication31-extra-inputs-v1.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(n): return json.loads((ROOT/n).read_bytes())
def safe(n):
    assert isinstance(n,str) and n and Path(n).as_posix()==n and not Path(n).is_absolute()
    assert not any(p in {'..','.git','.lake','__pycache__'} or re.fullmatch(r'checkpoint-\d+',p) for p in Path(n).parts[:-1])
    assert not any(c in n for c in '\0\r\n')
    p=ROOT/n; assert p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(ROOT)
    assert all(not q.is_symlink() for q in p.parents if q.is_relative_to(ROOT))
    return p

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--additional-peer',action='append',default=[])
args=ap.parse_args()
assert not OUT.exists()
manifest=read('reports/full-coverage/checkpoint-31-manifest.json')
assert manifest['status']=='formal_verification_passed_partial_coverage' and manifest['source_only_snapshot'] is True
assert manifest['old_snapshot_or_lake_tree_copied'] is False
frozen=manifest['frozen_inputs_sha256']; closure={}; original_raw_applied={}
def add(n,h=None):
    p=safe(n); actual=sha(p); assert h is None or actual==h,n
    if n in frozen:
        if actual!=frozen[n]:
            assert n=='book/coverage/applied.json' and actual==manifest['working_inputs_sha256'][n]
            original_raw_applied[n]=actual
        return
    assert n not in closure or closure[n]==actual,n
    closure[n]=actual
def tree(n):
    p=ROOT/n; assert p.is_dir() and not p.is_symlink()
    for f in sorted(p.rglob('*')):
        if f.is_file(): add(f.relative_to(ROOT).as_posix())
def peer(n):
    d=read(n); assert d['status'].startswith('passed') and d.get('errors',[])==[],n
    tree(Path(n).parent.as_posix())
    for path,h in d.get('required_evidence_artifacts_sha256',{}).items(): add(path,h)

binding_name='book/coverage/checks/future31-core/owner31-exact-reviewed-bindings-v1.json'
binding=read(binding_name);add(binding_name)
for r in binding['replacements']:
    add(r['candidate']['file'],r['candidate']['sha256'])
    peer(r['independent_mapping_peer']['file'])
plan_name='book/coverage/checks/future31-core/current81-canonical-plan6-v1.json'
plan=read(plan_name);add(plan_name)
for s in plan['sources']:
    for r in s['independent_source_peers']: peer(r['file'])
application=read('reports/full-coverage/source80-81-corrections-application-v3.json')
for r in application['applications']: peer(r['independent_semantic_review']['file'])
for directory in [
    'book/coverage/checks/future31-core/current81-canonical-pairs6-v1',
    'book/coverage/checks/future31-core/Core15NF-Applied21proof1NF-candidates-v1',
    'book/coverage/checks/future31-core/Core24-Core15NF-Applied21proof1NF-final-candidates-v2',
    'book/coverage/checks/future31-foundations/current81-four-family-real8-bound-v1',
    'book/coverage/checks/future31-foundations/current81-four-family-disjoint-inverse-v3',
    'book/coverage/checks/modules-future31/current81-integral39-ast19-realpair-v1',
    'book/coverage/checks/future31-applied/owner31-integrator-code4-independent-v1',
    'book/coverage/checks/future31-applied/export-freeze31-independent-v1',
    'book/coverage/checks/future31-core/runtime31-source81-independent-modules-v1',
    'book/coverage/checks/future31-core/source80-81-helper3-independent-foundations-v1',
    'book/coverage/checks/future31-core/source81-tmp-context-independent-modules-v1',
    'book/coverage/checks/future31-core/source81-installed-owner31-context-independent-modules-v1',
    'reports/full-coverage/lean-checkpoint-31',
    'reports/full-coverage/lean-checkpoint-31-source81-v1',
    'reports/full-coverage/browser-artifacts-31-changed2-v1',
    'reports/full-coverage/browser-artifacts-31-source81-changed-regions-v1',
    'reports/full-coverage/owner30-originals-before-owner31-integration-v4',
    'reports/full-coverage/source-history/approved-corrections80-81-20261012',
    'reports/full-coverage/source-history/documentation-before-checkpoint31-v1',
    'reports/full-coverage/source80-81-actual-application-parsers-v1',
]: tree(directory)
for n in args.additional_peer: peer(n)
readiness_name='book/coverage/checks/future31-core/current81-canonical-pairs6-v1/actual-reviewed31-canonical-paired-readiness-v1.json'
readiness=read(readiness_name)
add(readiness_name,'c18752bbf4b29ef8218cb28d990aad7edfcf0220babe2bacbafb3101bde43520')
assert readiness['status'].startswith('passed') and readiness['errors']==[]
assert readiness['source_count']==6 and len(readiness['actual_paired_records'])==12
for pair in readiness['actual_paired_records']:
    assert pair['actual_exit_code']==0
    for key in ['actual_record','raw_log','source_snapshot']:
        r=pair[key];add(r['file'],r['sha256'])
for n in [
    'book/README.md','verification/lean/README.md','reports/full-coverage/README.md','book/coverage/progress.json',
    'reports/full-coverage/checkpoint-31-selection.json','reports/full-coverage/checkpoint31-runtime-source81-preparation-v1.json',
    'reports/full-coverage/source80-81-corrections-application-v3.json','reports/full-coverage/owner31-reviewed-candidate-integration-v4.json',
    'reports/full-coverage/owner31-isolated-readonly-preflight-v1.json','reports/full-coverage/owner31-isolated-actual-apply-preflight-v1.json',
    'reports/full-coverage/source81-owner30-tmp-context-preparation-v1.json','reports/full-coverage/source81-installed-owner31-tmp-context-preparation-v1.json',
    'reports/full-coverage/integration-31-source81-v2.json','reports/full-coverage/browser-checkpoint-31-changed2-v1.json',
    'reports/full-coverage/browser31-source81-two-changed-regions-v1.json','reports/full-coverage/browser31-source81-changed-regions-Root-visual-v1.json',
    'reports/full-coverage/checkpoint31-documentation-preparation-v1.json','reports/full-coverage/publication30-finish-root-v1.json',
    'reports/full-coverage/live-checkpoint-30-attempt3.json',
    'reports/full-coverage/pages-checkpoint-30-attempt3.json','reports/full-coverage/pages-checkpoint-30-attempt3.log',
    'qa/source81_changed_regions31_v1.mjs','qa/learning_review.mjs','qa/book_browser_checks.mjs',
    'book/coverage/prepare_publication31_source_only_v1.py','book/coverage/freeze_checkpoint31_source_only_v1.py',
    'book/coverage/export_runtime_audit31_v1.py','book/coverage/prepare_checkpoint31_proof_selection_v1.py',
    'book/coverage/checks/root_record_actual29_v1.py','book/coverage/checks/root_finish_checkpoint30_delivery_v1.py',
    'book/coverage/checks/root_apply_source80_81_v1.py','book/coverage/checks/root_apply_source80_81_v2.py','book/coverage/checks/root_apply_source80_81_v3.py',
    'book/coverage/checks/root_prepare_source81_owner30_tmp_context_v1.py','book/coverage/checks/root_prepare_source81_installed_owner31_tmp_context_v1.py',
    'book/coverage/checks/run_root31_reviewed_canonical_pairs_v1.py','book/coverage/checks/root_prepare_canonical31_plan_v1.py',
    'book/coverage/checks/root_prepare_owner31_bindings_v1.py','book/coverage/checks/root_prepare_checkpoint31_runtime_v1.py',
    'book/coverage/checks/root_prepare_core_applied31_AST_candidates_v1.py','book/coverage/checks/root_bind_core24_AST31_candidates_v1.py',
    'book/coverage/checks/root_integrate_owner31_candidates_v4.py','book/coverage/checks/root_prepare_checkpoint31_documents_v1.py',
    'book/coverage/checks/root_prepare_publication31_supplements_v1.py','book/coverage/checks/root_prepare_publication31_supplements_v2.py','book/coverage/checks/root_prepare_publication31_supplements_v3.py',
]: add(n)
stems=[
    'pages30-metadata-jobs-observation-execution-v2','live30-metadata-confirmation-execution-v1','finish-checkpoint30-delivery-execution-v1',
    'source80-81-readonly-preflight-execution-v1','source80-81-readonly-preflight-execution-v2','source80-81-actual-application-execution-v1',
    'static31-source81-execution-v1','static31-source81-execution-v2','source81-owner30-tmp-context-preparation-execution-v1',
    'current81-canonical31-plan-preparation-execution-v1','current81-canonical31-readonly-preflight-execution-v1',
    'current81-canonical31-six-paired-application-execution-v1','prepare-checkpoint31-proof-selection-execution-v1',
    'Core15NF-Applied21proof1NF-draft-preparation-execution-v1','Core24-Core15NF-Applied21proof1NF-final-preparation-execution-v1',
    'owner31-binding-preparation-execution-v1','owner31-readonly-preflight-execution-v1','owner31-actual-application-execution-v1',
    'owner31-global-ledger-execution-v1','checkpoint31-runtime-source81-preparation-execution-v1',
    'verify-runtime-checkpoint31-source81-execution-v1','source81-installed-owner31-tmp-context-preparation-execution-v1',
    'export-runtime-checkpoint31-source81-execution-v1','freeze-checkpoint31-source-only-execution-v1',
    'freeze-checkpoint31-source-only-execution-v2','frozen-ledger31-source-only-execution-v1','prepare-documents31-execution-v1',
    'browser31-changed2-execution-v1','browser31-source81-changed-regions-execution-v1',
]
for stem in stems:
    for suffix in ['.json','.log']: add('reports/full-coverage/'+stem+suffix)
config=PUB/'_config.yml'; archive=ROOT/'reports/full-coverage/source-history/pages31-original-configuration-v1.yml'
assert not archive.exists() and sha(config)==sha(ROOT/'_config.yml')
shutil.copyfile(config,archive)
exclusions={l[4:] for l in config.read_text().splitlines() if l.startswith('  - ')}|{
    'reports/full-coverage/lean-checkpoint-30','reports/full-coverage/lean-checkpoint-30-final-css-v1',
    'reports/full-coverage/owner30-originals-before-owner31-integration-v4',
    'reports/full-coverage/source-history','reports/full-coverage/source80-81-actual-application-parsers-v1',
    'reports/full-coverage/publication31-extra-inputs-v1.json','reports/full-coverage/publication31-prepared-exact-files-v1.json',
    'reports/full-coverage/checkpoint-30-manifest.json','reports/full-coverage/checkpoint-30-selection.json',
}
for n in closure:
    if n.startswith('book/coverage/inventory-') and n.endswith('.json'): exclusions.add(n)
(ROOT/'_config.yml').write_text('# Preserve original audit evidence in Git; publish current readable site and audit.\nexclude:\n'+''.join('  - '+n+'\n' for n in sorted(exclusions)))
add('_config.yml');add(archive.relative_to(ROOT).as_posix())
copy={};existing={}
for n,h in sorted(closure.items()):
    if (PUB/n).is_file() and sha(PUB/n)==h: existing[n]=h
    else: copy[n]=h
assert closure=={n:sha(safe(n)) for n in closure}
record={'status':'explicit_source31_publication_supplement_paths_and_existing_historical_references',
    'copy_root_paths_sha256':copy,'unchanged_existing_publication_paths_sha256':existing,
    'source_only_manifest':{'file':'reports/full-coverage/checkpoint-31-manifest.json','sha256':sha(ROOT/'reports/full-coverage/checkpoint-31-manifest.json')},
    'current_original_raw_applied_ledger_preserved_at_reviewed_candidate_and_not_substituted_for_pruned_publication':original_raw_applied,
    'explicit_approved_additional_peers':args.additional_peer,'exact_current31_evidence_file_count':len(closure),
    'new_or_changed_supplement_count':len(copy),'unchanged_existing_publication_count':len(existing),
    'old_snapshot_or_lake_tree_copied':False,'coverage_complete':False,'commit_push_or_live_success_claimed':False}
with OUT.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':record['status'],'new_or_changed_files':len(copy),'new_or_changed_bytes':sum((ROOT/n).stat().st_size for n in copy),
    'existing_files':len(existing),'supplements_sha256':sha(OUT),'coverage_complete':False}))
