"""Check actual Source93 integration and freeze its selected proof runtime."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from build_foundations import check, SITE, AUTHOR

BASE='book/solutions/releases/source93-foundations-v1'
PRIOR='reports/solution-review/runtime-source92-piece02-v1'
RUNTIME='reports/solution-review/runtime-source93-foundations-v1'


def current():
    plan=h.read(BASE+'/edit-plan.json')
    actual=check(h.path(SITE).read_bytes(),h.path(AUTHOR).read_bytes(),plan)
    for name,info in plan['files'].items():assert h.ref(name)['sha256']==info['candidate']['sha256']
    assert h.read(BASE+'/installation.json')['status']==actual['status']
    return plan,actual


def integration():
    plan,actual=current()
    sys.path.insert(0,str(ROOT/'book'))
    import validate as v
    original=h.read('book/solutions/baseline-source90/manifest.json')
    source90={Path(name).name:h.path(ref['file']).read_text()
              for name,ref in original['source_snapshots'].items()
              if name.startswith('SafeLearning/') and Path(name).name!='case-studies.html'}
    report=v.validate(True,approved_preservation_sources=source90,
                      approved_practice_additions={'primer-basics.html':30})
    result=dict(status=report['status'],edit_plan=h.ref(BASE+'/edit-plan.json'),
                exact_current_preservation=h.ref(BASE+'/installation.json'),
                validator=h.ref('book/validate.py'),book_integration=report,
                limits='Source90 is used only to restore the historical pre-book comparison after exact Source92-to-Source93 preservation checks. Actual links, labs, counts, scripts and disposable builds use the installed Source93 content. No new independent agent review or formal coverage is inferred.')
    h.json_put(BASE+'/book-integration.json',result)
    assert report['status']=='PASS',report['errors']
    assert report['counts']['all_current_exercises']==586
    assert report['counts']['approved_practice_additions']==30
    assert report['build_idempotence']['current_root_already_matches_build']
    print(dict(status='passed_actual_book_integration',exercises=586,labs=21,pages=29))


def prepare_runtime():
    plan,actual=current()
    prior=h.read(PRIOR+'/reports/lean-verification/verification.json')
    assert prior['status']=='passed' and prior['proof_file_count']==1272
    expected={**prior['proof_sha256'],**prior['project_sha256']}
    expected['book/coverage/lean_names.py']=h.ref(PRIOR+'/book/coverage/lean_names.py')['sha256']
    for name,digest in expected.items():
        origin=ROOT/PRIOR/name;target=ROOT/RUNTIME/name
        assert h.sha(origin.read_bytes())==digest
        target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists():assert h.sha(target.read_bytes())==digest
        else:os.link(origin,target)
    site={}
    for name,ref in h.read(BASE+'/baseline-source92/manifest.json')['files'].items():
        if not name.startswith('SafeLearning/'):continue
        current_ref=h.ref(name)
        site[name]=current_ref['sha256']
        h.put(RUNTIME+'/'+name,h.path(name).read_bytes())
    assert len(site)==31
    for part in ('build','packages'):
        target=ROOT/RUNTIME/'verification/lean/.lake'/part
        origin=ROOT/'verification/lean/.lake'/part
        target.parent.mkdir(parents=True,exist_ok=True)
        if target.is_symlink():assert target.resolve()==origin.resolve()
        else:
            assert not target.exists()
            target.symlink_to(origin.resolve(),target_is_directory=True)
    actual_proofs={p.relative_to(ROOT/RUNTIME).as_posix():h.sha(p.read_bytes())
                   for p in (ROOT/RUNTIME/'verification/lean/SafeLearning').glob('*.lean')}
    assert actual_proofs==prior['proof_sha256']
    sys.path.insert(0,str(ROOT/'book'))
    import inventory_claims as inv
    inv.OUT=ROOT/BASE/'source93-inventory'
    if (inv.OUT/'inventory.json').exists():
        inventory=h.read(BASE+'/source93-inventory/inventory.json')
        assert inventory['source_sha256']=={k:v for k,v in site.items() if k.endswith('.html')}
        assert inventory['exercise_count_contract']==h.ref('book/exercise-counts.json')
    else:inv.inventory()
    inventory=h.read(BASE+'/source93-inventory/inventory.json')
    assert inventory['counts']['exercises']==586
    h.json_put(BASE+'/runtime-preparation.json',dict(status='prepared_selected_source93_runtime_no_new_formal_coverage',
        runtime=RUNTIME,previous_audit=h.ref(PRIOR+'/reports/lean-verification/verification.json'),
        site_sha256=site,proof_sha256=prior['proof_sha256'],project_sha256=prior['project_sha256'],
        inventory=h.ref(BASE+'/source93-inventory/inventory.json'),
        changed_proof_files=[],unselected_future_files_included=False,
        limits='The unchanged selected proof bundle is re-audited against new reader hashes. This does not formalize the thirty added questions or the fifty expanded answers.'))
    print(dict(status='prepared',selected_proof_files=1272,reader_assets=31,exercises=586))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['integration','prepare-runtime'])
    command=parser.parse_args().command
    integration() if command=='integration' else prepare_runtime()
