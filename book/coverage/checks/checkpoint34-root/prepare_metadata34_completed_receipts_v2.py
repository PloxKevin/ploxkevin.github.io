"""Bind finalized metadata inputs without hashing the active recorder's log."""
from datetime import datetime, timezone
import json
from install_owners34 import path, sha, ref, read, atomic, encode

OLD = 'reports/full-coverage/publication34-delivery-metadata-plan-v1.json'
OUT = 'reports/full-coverage/publication34-delivery-metadata-plan-v2.json'
COMPLETED = 'reports/full-coverage/prepare-delivery-metadata34-execution-v1.json'


def main():
    old = read(OLD)
    native = read(COMPLETED)
    assert old['status'] == 'exact_verified_content34_delivery_metadata_plan'
    assert native['status'] == 'passed' and native['actual_exit_code'] == 0
    assert native['helper_sha256_before'] == native['helper_sha256_after']
    assert all(sha(n) == h for n, h in native['helper_sha256_after'].items())
    assert sha(native['log']) == native['log_sha256']
    changed = {n: {'original_plan_sha256': h, 'completed_sha256': sha(n)}
               for n, h in old['paths_sha256'].items() if sha(n) != h}
    assert set(changed) == {native['log']}
    assert changed[native['log']]['original_plan_sha256'] == 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'
    hashes = {n: sha(n) for n in old['paths_sha256']}
    extra = [OLD, COMPLETED,
        'reports/full-coverage/commit-metadata34-execution-v1.json',
        'reports/full-coverage/commit-metadata34-execution-v1.log',
        'book/coverage/checks/checkpoint34-root/publish_metadata34_v2.py',
        'book/coverage/checks/checkpoint34-root/close_metadata_delivery34_v2.py',
        'book/coverage/checks/checkpoint34-root/prepare_metadata34_completed_receipts_v2.py']
    hashes.update({n: sha(n) for n in extra})
    assert not any(n.endswith('prepare-delivery-metadata34-execution-v2.log') for n in hashes)
    delivery = read('reports/full-coverage/publication34-content-delivery-v1.json')
    assert delivery['status'] == 'passed_actual_checkpoint34_content_push_Pages_and_all31_live_hashes'
    assert old['content_commit'] == delivery['content_commit']
    if path(OUT).exists():
        plan = read(OUT)
        assert plan['paths_sha256'] == hashes and plan['superseded_plan'] == ref(OLD)
    else:
        plan = {**old, 'created_at_utc': datetime.now(timezone.utc).isoformat(),
            'paths_sha256': hashes, 'superseded_plan': ref(OLD),
            'completed_prior_builder_receipt': ref(COMPLETED), 'corrected_completed_log_hashes': changed,
            'active_builder_native_record_and_log_included': False,
            'scope': 'Only completed inputs are bound. The original empty-log plan and failed metadata preflight remain unchanged. No metadata commit or deployment is inferred.'}
        atomic(OUT, encode(plan))
    print(json.dumps({'status': plan['status'], 'files': len(hashes), 'active_log_excluded': True, 'plan': ref(OUT)}))


if __name__ == '__main__':
    main()
