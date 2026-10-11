#!/usr/bin/env python3
"""Reproduce the source's finite-difference check; this is empirical, not a proof."""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import platform
import sys
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
SEED = 1242026
STEP = 1e-5
TOLERANCE = 1e-9


def certificate(first: np.ndarray, last: np.ndarray, multiplier: np.ndarray, gain: float) -> np.ndarray:
    hidden, inputs = first.shape
    outputs = last.shape[0]
    diagonal = np.diag(multiplier)
    return np.block([
        [gain * gain * np.eye(inputs), -first.T @ diagonal, np.zeros((inputs, outputs))],
        [-diagonal @ first, 2 * diagonal, -last.T],
        [np.zeros((outputs, inputs)), -last, np.eye(outputs)],
    ])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'book/coverage/checks/modules-logdet-finite-difference.json')
    args = parser.parse_args()
    generator = np.random.default_rng(SEED)
    cases = []
    all_error = []
    dataset_hash = hashlib.sha256()
    for inputs, hidden, outputs in ((1, 1, 1), (2, 3, 2), (3, 4, 2), (4, 2, 3)):
        for repetition in range(10):
            first = generator.normal(0, .15, (hidden, inputs))
            last = generator.normal(0, .15, (outputs, hidden))
            multiplier = generator.uniform(.7, 1.3, hidden)
            gain = 2.0
            matrix = certificate(first, last, multiplier, gain)
            minimum = float(np.linalg.eigvalsh(matrix)[0])
            np.linalg.cholesky(matrix)
            inverse = np.linalg.solve(matrix, np.eye(matrix.shape[0]))
            analytic = -2 * np.diag(multiplier) @ inverse[inputs:inputs + hidden, :inputs]
            finite = np.empty_like(first)
            perturbed_minimum = minimum
            for row in range(hidden):
                for column in range(inputs):
                    direction = np.zeros_like(first)
                    direction[row, column] = STEP
                    plus = certificate(first + direction, last, multiplier, gain)
                    minus = certificate(first - direction, last, multiplier, gain)
                    np.linalg.cholesky(plus)
                    np.linalg.cholesky(minus)
                    sign_plus, log_plus = np.linalg.slogdet(plus)
                    sign_minus, log_minus = np.linalg.slogdet(minus)
                    if sign_plus != 1 or sign_minus != 1:
                        raise RuntimeError('A finite-difference evaluation left the checked positive-definite region')
                    finite[row, column] = (log_plus - log_minus) / (2 * STEP)
                    perturbed_minimum = min(perturbed_minimum, float(np.linalg.eigvalsh(plus)[0]), float(np.linalg.eigvalsh(minus)[0]))
            error = np.abs(analytic - finite)
            all_error.extend(error.ravel().tolist())
            for array in (first, last, multiplier):
                dataset_hash.update(np.asarray(array, dtype='<f8').tobytes(order='C'))
            cases.append({
                'inputs': inputs, 'hidden': hidden, 'outputs': outputs, 'repetition': repetition,
                'first_weight': first.tolist(), 'last_weight': last.tolist(), 'multiplier': multiplier.tolist(),
                'gain': gain, 'analytic_gradient': analytic.tolist(), 'finite_difference_gradient': finite.tolist(),
                'max_absolute_error': float(error.max()), 'minimum_checked_eigenvalue': perturbed_minimum,
            })
    maximum = max(all_error)
    passed = maximum <= TOLERANCE
    result = {
        'generated_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'kind': 'reproducible_empirical_finite_difference_check', 'status': 'passed' if passed else 'failed',
        'script': str(Path(__file__).resolve().relative_to(ROOT)),
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'source_unit': 'lipsdp.html::node-1313', 'seed': SEED, 'step': STEP,
        'tolerance': TOLERANCE, 'case_count': len(cases), 'scalar_derivative_count': len(all_error),
        'max_absolute_error': maximum, 'dataset_sha256': dataset_hash.hexdigest(),
        'python': platform.python_version(), 'numpy': np.__version__, 'arithmetic': 'NumPy float64',
        'cases': cases,
        'limits': [
            'This reproduces a seeded numerical experiment on the literal source block certificate.',
            'The checked error is empirical float64 evidence; Lean proves the exact gradient separately.',
            'It does not recover an undocumented historical random run or validate a floating-point solver.',
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'case_count', 'scalar_derivative_count', 'max_absolute_error', 'dataset_sha256')}, indent=2))
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
