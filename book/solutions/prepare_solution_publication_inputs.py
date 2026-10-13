"""Select the bounded solution release and evidence, excluding runtimes and caches."""
import os
from pathlib import Path

import solution_review as review
import solution_release as release
import stage_solution_publication as staging

LIST='reports/solution-review/source91-content-publication-files-v1.json'


def main():
    plan=release.load_plan(review.ref(release.PLAN)['sha256'])
    ready=review.read('reports/solution-review/source91-release-ready-v1.json')
    assert ready['status']=='passed_source91_all556_release_ready_for_publication'
    files=set(plan['site_source91_sha256']) | {r['file'] for r in plan['files']}
    files.update(['README.md','book/coverage/progress.json','book/coverage/CONTINUATION.md',
                  'reports/full-coverage/README.md','verification/lean/README.md','book/validate.py',
                  'page_contract.md','qa/check.mjs','qa/learning_review.mjs','qa/book_browser_checks.mjs',
                  'qa/solution_visual91.mjs','qa/source91_math_scroll_probe.mjs','qa/source91_math_scroll_probe_v2.mjs',
                  'qa/package.json','qa/package-lock.json',LIST])
    for top in ['book/solutions','reports/solution-review']:
        for parent,directories,names in os.walk(review.ROOT/top,followlinks=False):
            directories[:]=[d for d in directories if d not in {'.git','.lake','__pycache__','source-objects'}
                and not d.startswith(('runtime-','isolated-runtime','archive')) and not (Path(parent)/d).is_symlink()]
            for name in names:
                path=Path(parent)/name
                if name.endswith(('.pyc','.lock','.olean','.ilean','.o','.trace')) or name.startswith('.') or path.is_symlink():continue
                files.add(path.relative_to(review.ROOT).as_posix())
    # Checkpoint35's final receipt was created after its last metadata commit.
    closure=review.read('reports/full-coverage/publication35-finish-v1.json')
    assert closure['status']=='passed_actual_checkpoint35_content_and_metadata_push_Pages_all31_delivery'
    files.add('reports/full-coverage/publication35-finish-v1.json')
    files.add('book/coverage/checks/checkpoint35-root/close_delivery35.py')
    for ref in closure['evidence']:
        release.exact(ref);files.add(ref['file'])
    assert len(files)<5000
    for name in files:
        staging.target(name)
        if name!=LIST:
            source=review.path(name)
            assert source.is_file() and source.stat().st_size<95_000_000,name
    review.json_put(LIST,sorted(files))
    print({'files':len(files),'bytes':sum(review.path(n).stat().st_size for n in files),
           'excluded_runtime_and_cache':True,'file_list':review.ref(LIST)})


if __name__=='__main__':main()
