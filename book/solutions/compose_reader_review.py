"""Compose exact passing page checks from native attempts without hiding failed runs."""
import argparse
import copy
import json
from pathlib import Path

import solution_review as review
import solution_release as release


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt',action='append',required=True,help='Completed native reader QA receipt, oldest first')
    parser.add_argument('--report',required=True)
    args=parser.parse_args()
    plan=release.load_plan(review.ref(release.PLAN)['sha256'])
    expected={Path(n).name:h for n,h in plan['site_source91_sha256'].items() if n.endswith('.html')}
    selected={};attempts=[];failures=[]
    for name in args.attempt:
        native=review.read(name)
        assert native['status'] in {'passed','failed'} and native['actual_exit_code'] in {0,1}
        assert native['helper_sha256_before']==native['helper_sha256_after'] and not native['binding_errors_after']
        assert review.ref(native['log'])['sha256']==native['log_sha256']
        command=native['actual_command']
        assert command[:2]==['node','qa/learning_review.mjs'] and native['actual_workdir']==str(review.ROOT)
        for helper in ('qa/learning_review.mjs','qa/book_browser_checks.mjs'):
            assert native['helper_sha256_before'][helper]==review.ref(helper)['sha256']
        for asset,h in plan['site_source91_sha256'].items():assert native['helper_sha256_before'][asset]==h
        assert '--report' in command
        browser_name=command[command.index('--report')+1]
        browser=review.read(browser_name)
        assert isinstance(browser,list) and browser
        assert len({r['file'] for r in browser})==len(browser)
        assert native['actual_exit_code']==(0 if all(r['status']=='passed' for r in browser) else 1)
        attempts.append({'native':review.ref(name),'browser':review.ref(browser_name),'native_status':native['status'],
                         'actual_exit_code':native['actual_exit_code']})
        for index,row in enumerate(browser):
            assert row['file'] in expected and row['source_sha256']==expected[row['file']]
            assert row['qa_source_sha256']=={Path(h).name:review.ref(h)['sha256'] for h in ('qa/learning_review.mjs','qa/book_browser_checks.mjs')}
            assert row['status'] in {'passed','failed'},'Incomplete page attempt'
            if row['status']=='failed':
                assert row['errors']
                selected.pop(row['file'],None)
                failures.append({'file':row['file'],'errors':row['errors'],'native':review.ref(name),
                                 'browser':review.ref(browser_name),'row_index':index})
                continue
            assert not row['errors']
            assert {v['width'] for v in row['viewports']}=={320,390,768,820,1280}
            value=copy.deepcopy(row)
            value['native_attempt_origin']={'native':review.ref(name),'browser':review.ref(browser_name),'row_index':index,
                                            'containing_native_attempt_status':native['status']}
            selected[row['file']]=value
    assert selected.keys()==expected.keys(),'Some reader pages have no complete passing native check'
    assert sum(r['exerciseCounts']['total'] for r in selected.values())==556
    report={'status':'passed_all29_reader_pages_from_exact_native_attempts','helper':review.ref(Path(__file__).relative_to(review.ROOT).as_posix()),
            'plan':review.ref(release.PLAN),'native_attempts':attempts,'preserved_failed_page_attempts':failures,
            'pages':[selected[n] for n in sorted(selected)],
            'scope':'Every selected row is copied from an actual complete passing page check with matching source/QA hashes. Earlier failed whole runs and page errors remain explicit and unchanged; no retry is fabricated.'}
    review.json_put(args.report,report)
    print(json.dumps({'status':report['status'],'pages':len(selected),'preserved_failed_pages':len(failures),'report':review.ref(args.report)}))


if __name__=='__main__':main()
