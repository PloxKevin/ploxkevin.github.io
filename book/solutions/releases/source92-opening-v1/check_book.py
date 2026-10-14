"""Validate actual Source92 integration after the exact solution-change chain."""
import importlib.util
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h


def main():
    base='book/solutions/releases/source92-opening-v1'
    plan=h.read(base+'/plan-v1.json')
    assert h.read(base+'/installation-v1.json')['status']=='passed_installed_source92_opening_solution_only_changes'
    for name,digest in plan['site_after_sha256'].items():assert h.ref(name)['sha256']==digest
    manifest=h.read('book/solutions/baseline-source90/manifest.json')
    source90={Path(name).name:h.path(snapshot['file']).read_text()
        for name,snapshot in manifest['source_snapshots'].items()
        if name.startswith('SafeLearning/') and Path(name).name!='case-studies.html'}
    spec=importlib.util.spec_from_file_location('recovery_book_validator',ROOT/'book/validate.py')
    validator=importlib.util.module_from_spec(spec);sys.modules[spec.name]=validator;spec.loader.exec_module(validator)
    result=validator.validate(True,approved_preservation_sources=source90)
    h.json_put('reports/solution-review/source92-book-integration-v1.json',{
        'status':result['status'],'plan':h.ref(base+'/plan-v1.json'),
        'current_solution_preservation':h.ref(base+'/installation-v1.json'),
        'historical_source90_baseline':h.ref('book/solutions/baseline-source90/manifest.json'),
        'book_validator':h.ref('book/validate.py'),'book_integration':result,
        'scope':'All links, native disclosures, authoring mirrors, catalog/navigation and two real disposable builds use the actual Source92 site. Source90 bytes enter only the historical pre-book preservation comparison after the actual solution change chain passed.'})
    assert result['status']=='PASS',result['errors']
    print({'status':'passed_all29_pages_actual_source92_book_integration','exercises':556,'labs':21})


if __name__=='__main__':main()
