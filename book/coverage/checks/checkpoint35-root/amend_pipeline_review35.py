"""Bind a current static runtime review alongside historical pipeline tests."""
from pathlib import Path
import hashlib
import json
import os

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
PRIOR = HERE / 'pipeline-writer-tests-v3.json'
CURRENT = HERE / 'prepare_runtime35.py'
OUT = HERE / 'pipeline-review-amendment-v4.json'


def ref(p):
    return dict(file=p.relative_to(ROOT).as_posix(), sha256=hashlib.sha256(p.read_bytes()).hexdigest())


def main():
    prior = json.loads(PRIOR.read_bytes())
    assert prior['status'] == 'passed' and prior['actual_exit_code'] == 0
    assert prior['input_sha256_before'] == prior['input_sha256_after']
    expected = next(r['sha256'] for r in prior['input_sha256_before'] if r['file'] == CURRENT.relative_to(ROOT).as_posix())
    source = CURRENT.read_text()
    new = "            exact(peer['inventory'])\n            assert peer['inventory']['sha256'] == plan['inventory']['sha256']"
    assert source.count(new) == 1
    inventories = [ROOT / 'book/coverage/inventory.json', ROOT / 'book/coverage/inventory-after-correction90.json']
    attempts = [ROOT / ('reports/full-coverage/prepare-runtime35-execution-v' + str(i) + '.json') for i in (1, 2)]
    inputs = [PRIOR, CURRENT, *inventories, *attempts, Path(__file__).resolve()]
    before = [ref(p) for p in inputs]
    assert before[2]['sha256'] == before[3]['sha256']
    assert json.loads(attempts[0].read_bytes())['status'] == 'failed'
    successful = json.loads(attempts[1].read_bytes())
    assert successful['status'] == 'passed' and successful['actual_exit_code'] == 0
    assert successful['helper_sha256_before'] == successful['helper_sha256_after']
    assert successful['helper_sha256_after'][CURRENT.relative_to(ROOT).as_posix()] == ref(CURRENT)['sha256']
    value = dict(status='passed_independent_current_runtime_inventory_alias_review',
        supersedes_current_runtime_source_binding_only=ref(PRIOR),
        tested_previous_runtime_sha256=expected, current_runtime_source=ref(CURRENT),
        current_static_review=[
            'Require the peer inventory file to exist with its recorded SHA256, then compare its SHA256 with the exact plan inventory SHA256.',
            'Match reviewed proof sources by file and SHA256, allowing extra bytes metadata in a peer reference.',
            'Source-only hardlink/object staging and deterministic exact-byte output comparison remain sound; caches are explicit runtime-only symlinks.',
            'No exact one-line diff against the historical v3 revision is claimed.'],
        inventory_aliases=[ref(p) for p in inventories],
        assessment='Both Source90 inventory filenames have identical exact bytes. The change preserves content identity and separately validates the peer file; it permits differing provenance filenames.',
        pipeline_tests_from_v3_remain_applicable=True, full_tests_repeated=False,
        actual_prior_failed_attempt=ref(attempts[0]), actual_completed_preparation_attempt=ref(attempts[1]),
        aggregate_or_client_crash_diagnosis_claimed=False, input_sha256_before=before,
        input_sha256_after=[ref(p) for p in inputs])
    assert value['input_sha256_before'] == value['input_sha256_after']
    with OUT.open('x') as output:
        json.dump(value, output, indent=2)
        output.write('\n')
        output.flush()
        os.fsync(output.fileno())
    print(json.dumps(dict(status=value['status'], record=OUT.relative_to(ROOT).as_posix(), current_runtime_sha256=ref(CURRENT)['sha256'])))


if __name__ == '__main__':
    main()
