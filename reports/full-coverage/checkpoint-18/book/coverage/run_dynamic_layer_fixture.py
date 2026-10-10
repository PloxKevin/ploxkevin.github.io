#!/usr/bin/env python3
"""Reproduce the precise length-four, two-input/three-output, 200-pair check.

All matrix entries, trajectories and energy ratios use fractions. This is a
finite reproducible experiment; the generic certificate implication is proved
separately in CompleteModulesDynamicLayerTrajectory/FiniteDynamicNetwork.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import random


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def multiply(first, second):
    return [[sum((a * b for a, b in zip(row, column)), Q(0))
             for column in zip(*second)] for row in first]


def subtract(first, second):
    return [[a - b for a, b in zip(left, right)]
            for left, right in zip(first, second)]


def negative(matrix):
    return [[-entry for entry in row] for row in matrix]


def identity(size):
    return [[Q(row == column) for column in range(size)] for row in range(size)]


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, list):
        return [encode(item) for item in value]
    if isinstance(value, dict):
        return {key: encode(item) for key, item in value.items()}
    return value


def actual_ldlt(matrix):
    size = len(matrix)
    lower = identity(size)
    diagonal = []
    for column in range(size):
        pivot = matrix[column][column] - sum(
            (lower[column][k] ** 2 * diagonal[k] for k in range(column)), Q(0))
        assert pivot > 0
        diagonal.append(pivot)
        for row in range(column + 1, size):
            lower[row][column] = (matrix[row][column] - sum(
                (lower[row][k] * diagonal[k] * lower[column][k]
                 for k in range(column)), Q(0))) / pivot
    diag_matrix = [[diagonal[row] if row == column else Q(0)
                    for column in range(size)] for row in range(size)]
    assert multiply(multiply(lower, diag_matrix), transpose(lower)) == matrix
    return lower, diagonal


def main():
    seed, pair_count, input_horizon = 746, 200, 40
    input_channels, output_channels, tap_count = 2, 3, 4
    rng = random.Random(seed)
    kernel = [[[Q(rng.randint(-10, 10), 2000)
                for _ in range(input_channels)] for _ in range(output_channels)]
              for _ in range(tap_count)]
    bias = [Q(rng.randint(-4, 4), 100) for _ in range(output_channels)]
    state_size = (tap_count - 1) * input_channels
    A = [[Q(row == column + input_channels)
          for column in range(state_size)] for row in range(state_size)]
    B = [[Q(row == column) for column in range(input_channels)]
         for row in range(state_size)]
    C = [[kernel[1 + state // input_channels][out][state % input_channels]
          for state in range(state_size)] for out in range(output_channels)]
    D = kernel[0]
    storage_diagonal = [Q(tap_count - 1 - state // input_channels, tap_count)
                        for state in range(state_size)]
    P = [[storage_diagonal[row] if row == column else Q(0)
          for column in range(state_size)] for row in range(state_size)]
    Xin, Xout, multiplier = identity(input_channels), identity(output_channels), identity(output_channels)
    AtP, BtP = multiply(transpose(A), P), multiply(transpose(B), P)
    top_left = subtract(P, multiply(AtP, A))
    top_middle = negative(multiply(AtP, B))
    top_right = negative(multiply(transpose(C), multiplier))
    middle_left = negative(multiply(BtP, A))
    middle_middle = subtract(Xin, multiply(BtP, B))
    middle_right = negative(multiply(transpose(D), multiplier))
    bottom_left, bottom_middle = negative(multiply(multiplier, C)), negative(multiply(multiplier, D))
    bottom_right = subtract([[2 * entry for entry in row] for row in multiplier], Xout)
    certificate = ([top_left[row] + top_middle[row] + top_right[row] for row in range(state_size)]
                   + [middle_left[row] + middle_middle[row] + middle_right[row] for row in range(input_channels)]
                   + [bottom_left[row] + bottom_middle[row] + bottom_right[row] for row in range(output_channels)])
    assert certificate == transpose(certificate)
    margins = [row[index] - sum((abs(entry) for j, entry in enumerate(row) if j != index), Q(0))
               for index, row in enumerate(certificate)]
    assert all(margin > 0 for margin in margins)
    lower, pivots = actual_ldlt(certificate)
    output_horizon = input_horizon + tap_count - 1

    def simulate(signal):
        state = [Q(0)] * state_size
        output = []
        for step in range(output_horizon):
            incoming = signal[step] if step < input_horizon else [Q(0)] * input_channels
            preactivation = [sum((C[out][s] * state[s] for s in range(state_size)), Q(0))
                             + sum((D[out][i] * incoming[i] for i in range(input_channels)), Q(0))
                             + bias[out] for out in range(output_channels)]
            direct = [sum((kernel[tap][out][channel] * signal[step - tap][channel]
                           for tap in range(tap_count) if 0 <= step - tap < input_horizon
                           for channel in range(input_channels)), Q(0)) + bias[out]
                      for out in range(output_channels)]
            assert preactivation == direct
            output.append([max(value, Q(0)) for value in preactivation])
            state = incoming + state[:state_size - input_channels]
        assert state == [Q(0)] * state_size
        return output

    records = []
    for pair in range(pair_count):
        first = [[Q(rng.randint(-32, 32), 8) for _ in range(input_channels)]
                 for _ in range(input_horizon)]
        second = [[Q(rng.randint(-32, 32), 8) for _ in range(input_channels)]
                  for _ in range(input_horizon)]
        first_output, second_output = simulate(first), simulate(second)
        input_energy = sum(((a - b) ** 2 for left, right in zip(first, second)
                            for a, b in zip(left, right)), Q(0))
        output_energy = sum(((a - b) ** 2 for left, right in zip(first_output, second_output)
                             for a, b in zip(left, right)), Q(0))
        assert input_energy > 0
        ratio = output_energy / input_energy
        assert ratio < 1
        records.append({"pair": pair, "input_squared_energy": input_energy,
                        "output_squared_energy": output_energy, "squared_gain_ratio": ratio})
    max_ratio = max(record["squared_gain_ratio"] for record in records)
    result = {"status": "passed", "source_unit_key": "lipsdp.html::node-646",
              "seed": seed, "pair_count": pair_count, "input_horizon": input_horizon,
              "output_horizon_including_zero_padding_flush": output_horizon,
              "input_channels": input_channels, "output_channels": output_channels,
              "tap_count": tap_count, "state_dimension": state_size,
              "activation": "ReLU", "linear_output_layer": "identity",
              "arithmetic": "exact fractions", "kernel_draw": "integers[-10,10]/2000",
              "signal_draw": "integers[-32,32]/8", "kernel_by_tap": kernel, "bias": bias,
              "A": A, "B": B, "C": C, "D": D, "P": P, "Xin": Xin, "Xout": Xout,
              "multiplier": multiplier, "literal_layer_certificate": certificate,
              "strict_row_diagonal_dominance_margins": margins,
              "exact_ldlt_lower_factor": lower, "exact_ldlt_positive_pivots": pivots,
              "all_ldlt_reconstruction_entries_equal": True,
              "all_state_preactivations_equal_zero_padded_convolution": True,
              "all_ratios_strictly_below_one": True, "maximum_squared_gain_ratio": max_ratio,
              "maximum_squared_gain_ratio_decimal": float(max_ratio), "pairs": records,
              "limits": ["This is one reproducible finite empirical fixture with the source dimensions and pair count.",
                         "It does not assert the original unpublished random seed or kernel was the same.",
                         "The all-model/all-horizon certificate theorem is separate Lean evidence."]}
    root = Path(__file__).resolve().parents[2]
    destination = root / "book/coverage/checks/modules-dynamic-layer-random-fixture-v1.json"
    destination.write_text(json.dumps(encode(result), indent=2) + "\n")
    print(json.dumps({"status": result["status"], "pair_count": pair_count,
                      "maximum_squared_gain_ratio_decimal": float(max_ratio),
                      "minimum_certificate_dominance_margin": str(min(margins)),
                      "positive_ldlt_pivot_count": len(pivots), "output": str(destination.relative_to(root))}))


if __name__ == "__main__":
    main()
