"""Prepare Source91 HTML with exactly the checkpoint35 selected proof sources.

The native audit runs separately. No unselected canonical proof file is added,
and no updated HTML-to-proof correspondence is inferred from a passing build.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile

import solution_review as review
import solution_release as release

ROOT=review.ROOT
PRIOR='reports/full-coverage/runtime-checkpoint-35-source90-v1'
RUNTIME='reports/solution-review/runtime-source91-selected35-v1'
REPORT='reports/solution-review/source91-runtime-preparation-v1.json'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan-sha256',required=True)
    args=parser.parse_args()
    plan=release.load_plan(args.plan_sha256)
    prior=review.read(release.PRIOR_AUDIT)
    assert prior['status']=='passed' and prior['proof_file_count']==1267 and prior['theorem_count']==11472
    assert review.ref(release.PRIOR_AUDIT)==plan['selected_prior_proof_audit']
    proof_hashes=prior['proof_sha256'];assert len(proof_hashes)==1267
    files={n:review.ref(PRIOR+'/'+n) for n in proof_hashes}
    for name,fingerprint in proof_hashes.items():
        assert files[name]['sha256']==fingerprint
    for name,fingerprint in prior['project_sha256'].items():
        files[name]=review.ref(PRIOR+'/'+name)
        assert files[name]['sha256']==fingerprint
    name='book/coverage/lean_names.py';files[name]=review.ref(PRIOR+'/'+name)
    for name,fingerprint in plan['site_source91_sha256'].items():
        files[name]=review.ref(name);assert files[name]['sha256']==fingerprint
    assert len(files)==1267+5+1+31
    expected_proofs={Path(n).name for n in proof_hashes}
    proof_directory=review.path(RUNTIME+'/verification/lean/SafeLearning')
    if proof_directory.exists():
        assert all(p.parent==proof_directory and p.name in expected_proofs and not p.is_symlink()
                   for p in proof_directory.rglob('*.lean')), 'Unselected proof source already exists in the runtime'
    expected_assets={Path(n).name for n in plan['site_source91_sha256']}
    site_directory=review.path(RUNTIME+'/SafeLearning')
    if site_directory.exists():
        assert all(p.name in expected_assets and not p.is_symlink() for p in site_directory.iterdir()
                   if p.suffix in {'.html','.js','.css'}), 'Unexpected runtime site asset'
    modules={Path(n).stem for n in proof_hashes}
    aggregate=release.exact(files['verification/lean/SafeLearning.lean']).read_text().splitlines()
    assert len(aggregate)==1267 and set(aggregate)=={'import SafeLearning.'+n for n in modules}
    objects=[]
    for target,source in sorted(files.items()):
        raw=release.exact(source).read_bytes()
        fingerprint=review.sha(raw)
        blob=RUNTIME+'/source-objects/'+fingerprint
        review.put(blob,raw)
        os.chmod(review.path(blob),0o444)
        path=review.path(RUNTIME+'/'+target,writable=True)
        if path.exists():
            assert review.sha(path.read_bytes())==fingerprint
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            os.link(review.path(blob),path)
        assert not path.is_symlink()
        objects.append({'runtime_file':RUNTIME+'/'+target,'sha256':fingerprint,'source':source,'object':blob})
    assert {p.name for p in proof_directory.glob('*.lean')}==expected_proofs
    assert {p.name for p in site_directory.iterdir() if p.suffix in {'.html','.js','.css'}}==expected_assets
    # Runtime-only links share already pinned dependency/build caches. Their
    # contents are checked by the real verifier; they are never published.
    lake=review.path(RUNTIME+'/verification/lean')/'.lake';lake.mkdir(exist_ok=True)
    for name in ('packages','build'):
        expected=(ROOT/'verification/lean/.lake'/name).resolve();assert expected.is_dir()
        target=lake/name
        if target.exists() or target.is_symlink():
            assert target.is_symlink() and target.resolve()==expected
        else:
            target.symlink_to(expected,target_is_directory=True)
    # Inventory the new source version into its own queue. The Source90 formal
    # inventory and owner ledgers remain exact historical evidence.
    sys.path.insert(0,str(ROOT/'book'))
    spec=importlib.util.spec_from_file_location('solution_source91_inventory',ROOT/'book/inventory_claims.py')
    inventory=importlib.util.module_from_spec(spec);spec.loader.exec_module(inventory)
    inventory_name=release.RELEASE+'/source91-inventory/inventory.json'
    if not review.path(inventory_name).exists():
        parent=review.path(release.RELEASE,writable=True)
        parent.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='.inventory-source91-',dir=parent) as temporary:
            inventory.OUT=Path(temporary)
            inventory.inventory()
            raw=(inventory.OUT/'inventory.json').read_bytes()
            value=json.loads(raw)
            assert value['counts']['exercises']==556 and value['source_sha256']=={
                n:h for n,h in plan['site_source91_sha256'].items() if n.endswith('.html')}
            review.put(inventory_name,raw)
    current=review.read(inventory_name)
    assert current['status']=='inventory_only_no_coverage_claim' and current['counts']['exercises']==556
    assert current['source_sha256']=={n:h for n,h in plan['site_source91_sha256'].items() if n.endswith('.html')}
    result={'status':'prepared_source91_selected35_runtime_native_audit_pending','plan':review.ref(release.PLAN),
            'helper':review.ref(Path(__file__).relative_to(ROOT).as_posix()),'runtime':RUNTIME,
            'prior_native_audit':review.ref(release.PRIOR_AUDIT),'proof_files':1267,'public_theorems':11472,
            'selected_proof_sources_unchanged':True,'unselected_proof_sources_added':0,
            'all31_site_source91_sha256':plan['site_source91_sha256'],'source_objects':objects,
            'new_inventory':review.ref(inventory_name),'new_inventory_counts':current['counts'],
            'cache_symlinks_runtime_only':True,'archives_or_prior_snapshot_trees_copied':False,
            'formal_source_correspondence_rebase':'pending_for_rewritten_solutions_no_automatic_status_promotion'}
    review.json_put(REPORT,result)
    print(json.dumps({'status':result['status'],'runtime':RUNTIME,'proof_files':1267,'report':review.ref(REPORT)}))


if __name__=='__main__':
    main()
