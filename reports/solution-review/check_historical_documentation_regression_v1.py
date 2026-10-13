"""Run the isolated writer test on exact recovered pre-fix helper bytes."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_final_documentation_independent_v1 as writer_test

writer_test.HELPER = 'reports/solution-review/source-history/prepare-solution-documentation-before-final-reporting-fixes-v1.py'

if __name__ == '__main__':
    raise SystemExit(writer_test.main())
