"""Read every frozen25 input and report exact current working-byte differences."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'reports/full-coverage/baseline25-working-inputs-before-owner26-observation-v1.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    assert not OUT.exists()
    path = ROOT / 'reports/full-coverage/checkpoint-25-manifest.json'
    manifest = json.loads(path.read_text())
    assert manifest['status'] == 'formal_verification_passed_partial_coverage'
    assert len(manifest['proof_files']) == 1156
    snapshot = ROOT / manifest['snapshot']
    for name, digest in manifest['frozen_inputs_sha256'].items():
        assert sha(snapshot / name) == digest, name
    differences = []
    for name, digest in manifest['working_inputs_sha256'].items():
        original = snapshot / name
        current = ROOT / name
        observed = sha(current) if current.is_file() else None
        if observed != digest:
            differences.append({'file': name, 'original_working_sha256': digest,
                'current_working_sha256': observed,
                'immutable_frozen_original': {'file': original.relative_to(ROOT).as_posix(),
                    'sha256': sha(original)}})
    for name, row in manifest['proof_files'].items():
        assert sha(ROOT / name) == row['sha256'], name
    record = {'status': 'read_only_complete_frozen25_to_current53_working_input_difference_observation',
        'observed_at_utc': datetime.now(timezone.utc).isoformat(),
        'manifest': {'file': path.relative_to(ROOT).as_posix(), 'sha256': sha(path)},
        'original_working_input_count': len(manifest['working_inputs_sha256']),
        'all_frozen_original_input_count': len(manifest['frozen_inputs_sha256']),
        'all_frozen_original_bytes_exact': True, 'all1156_selected25_source_bytes_exact': True,
        'different_rows': differences,
        'scope': 'Read-only byte observation before owner26 installation. This report authorizes no working delta and adds no mathematical or compiler approval.'}
    with OUT.open('x') as stream:
        stream.write(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': 'passed_read_only_observation', 'working_inputs': len(manifest['working_inputs_sha256']),
                      'frozen_inputs': len(manifest['frozen_inputs_sha256']),
                      'different_files': [row['file'] for row in differences]}))


if __name__ == '__main__':
    main()
