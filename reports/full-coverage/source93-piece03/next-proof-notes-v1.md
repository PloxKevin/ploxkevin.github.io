# Next numerical piece: preparation, not completed coverage

The current source still prints `E[N] ≈ 1.484230454`, along with the first-tail
value near `9.86588e-10`, transient rows and the stationary comparison. Existing
`CompleteModulesLandscapeARCountNumerics` bounds the count only between
`1.48415` and `1.484355`. It cannot certify the new nine-digit display.

The existing fifty-term integral bound in
`CompleteAppliedGaussianTailIntegral` has error at most `4e-16` through radius
four. Most monitored standardized thresholds lie within this interval. The
existing numerical bridge uses only the normalizer enclosure
`0.3989422 < 1/sqrt(2*pi) < 0.3989424`; its width is a precision bottleneck.
Mathlib's `Analysis/Real/Pi/Bounds.lean` provides `Real.pi_gt_d20` and
`Real.pi_lt_d20`. These can support a much tighter rational normalizer enclosure
by squared positive inequalities, without assuming a numerical square root.

The first standardized threshold is six. The radius-four polynomial theorem
does not cover it; a higher-degree rational exponential-series bound, or a
rigorous positive tail enclosure, is needed. The generic ratio/error theorem
already exists in `CompleteAppliedGaussianGeneralIntegral`.

Use rational intervals for the standardized thresholds, monotonicity of the
actual Gaussian tail, and rational endpoint integral bounds. Track all forty
term errors so the sum proves the required displayed precision. Decimal
recomputation alone is not a Lean enclosure. Keep the stationary approximation,
same-process covariance/dependence, Markov cap and empirical joint simulation
as separate claims. No new part(iii) completion credit is claimed here.
