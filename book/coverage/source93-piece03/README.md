# Source93 formal piece 03: Gaussian-tail rounding

This piece adds **22 Lean theorems in two modules** for the numerical warning
in Landscape Exercise 1.5(ii). The selected bundle passes **11,544 theorems in
1,274 files**. Both new modules received fresh kernel replays; the other 1,272
checks retain exact prior source/import and dependency evidence. The aggregate
build and the standard-axiom audit of every theorem ran again. Only `propext`,
`Classical.choice` and `Quot.sound` are used. See the [actual audit](../../../reports/full-coverage/runtime-source93-piece03-v1/reports/lean-verification/verification.json)
and [native command receipt](../../../reports/full-coverage/source93-piece03/selected-audit-native-v1.json).

The proofs construct a finite set from binary64 exponent and fraction fields,
including gradual subnormal values, and choose a nearest representable value.
They prove the gap below one is at least `2^-53` and the positive-value floor
is `2^-1074`. The encoding and nearest-rounding interpretation follow the
[official Double specification](https://docs.oracle.com/en/java/javase/24/docs/api/java.base/java/lang/Double.html).
Strict inequalities avoid dependence on a tie-breaking policy.

The actual standard Gaussian upper tail tends to zero and stays positive at
every finite threshold. These facts give finite thresholds where rounding the
CDF to one and subtracting gives a false zero, and more extreme thresholds where
even a directly evaluated tail rounds to zero. Continuity supplies a finite
nonnegative threshold with true tail `2^-60`: that value is representable and
survives direct rounding, while CDF subtraction loses it.

The second module connects this example to the original recurrence, with
`k=1/2`, `sigma=1` and `T=1`. A constructed real goal makes its actual
infinite-path expected unsafe count equal `2^-60 > 0`. The rounded CDF sum for
that same expectation is zero; direct evaluation retains the positive value.
The one-term sum introduces no separate summation-rounding assumption.

The [exact clause packet](claims-v1.json) and [ledger](ledger-v1.json) bind the
reader page, paragraph bytes, inventory, proof sources, hypotheses and model
limits. The three new mathematical clause mappings are **self-reviewed**;
independent source-to-statement review is pending. A separate reviewer was
requested asynchronously because this session requires explicit authorization
before delegating. None has been authorized or claimed. The independently
reviewed total stays at **27 clauses and 12 complete leaves**, with **zero newly
completed leaves or exercises**. Exercise 1.5 and full book coverage remain
incomplete. The new model is a concrete checked candidate for closing the
mixed numerical paragraph after that review.

This models rounding exact real function values into the specified finite
format. It does not verify hardware/compiler primitives, input rounding,
a JavaScript `erfc` approximation, an arbitrary numerical library, or the
nine-digit values in part (iii). Direct evaluation is not claimed always to
return a nonzero or exact answer. The worked comparison in part (iii) remains
separate from the constructed one-step counterexample.

All 31 reader assets are unchanged, so Source93's exact browser, print,
arithmetic and integration evidence remains applicable. All eighty foundation
answers still await current formal correspondence; this piece grants them no
credit. Eight canonical future proof files remain unselected and unpublished.

For the workspace, reproduce in the selected runtime using a fresh report path:

```sh
cd reports/full-coverage/runtime-source93-piece03-v1
python3 -B verification/lean/verify.py --output reports/reproduction-v1
```

In a clean published checkout the same selected proofs occupy their normal
paths. Preserve prior reports when reproducing. Actual content and metadata
delivery are recorded separately; a final receipt is kept locally after the
last observed delivery and included with the next checkpoint.
