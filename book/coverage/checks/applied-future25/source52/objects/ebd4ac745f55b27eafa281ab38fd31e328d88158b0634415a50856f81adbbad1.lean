import SafeLearning.CompleteAppliedFiniteKLSupport
import SafeLearning.CompleteAppliedInformation
import Mathlib.Analysis.Convex.Deriv
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedBinaryPinsker
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedTwoAtomRisk SafeLearning.CompleteAppliedInformation
open SafeLearning.CompleteAppliedFiniteKLSupport
open scoped ENNReal NNReal Classical

def pinskerPotential (q x : ℝ) : ℝ :=
  x*Real.log x+(1-x)*Real.log (1-x)-x*Real.log q-
    (1-x)*Real.log (1-q)-2*(x-q)^2
def pinskerFirst (q x : ℝ) : ℝ :=
  Real.log x-Real.log (1-x)-Real.log q+Real.log (1-q)-4*(x-q)
def pinskerSecond (x : ℝ) : ℝ := 1/x+1/(1-x)-4

theorem potential_continuous (q : ℝ) : Continuous (pinskerPotential q) := by
  unfold pinskerPotential
  exact ((((Real.continuous_mul_log.add
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).sub
    (continuous_id.mul continuous_const)).sub
    ((continuous_const.sub continuous_id).mul continuous_const)).sub
    (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)))

theorem potential_has_derivative (q x : ℝ) (hx : x∈Set.Ioo (0:ℝ) 1) :
    HasDerivAt (pinskerPotential q) (pinskerFirst q x) x := by
  have hd:=((((Real.hasDerivAt_mul_log (ne_of_gt hx.1)).add
    ((Real.hasDerivAt_mul_log (show 1-x≠0 by linarith [hx.2])).comp x
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x)))).sub
    ((hasDerivAt_id x).mul_const (Real.log q))).sub
    (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul_const (Real.log (1-q)))).sub
    ((((hasDerivAt_id x).sub_const q).pow 2).const_mul 2)
  convert hd using 1
  · funext y
    dsimp [pinskerPotential]
  · dsimp [pinskerFirst]
    ring

theorem potential_second_derivative (q x : ℝ) (hx : x∈Set.Ioo (0:ℝ) 1) :
    HasDerivAt (pinskerFirst q) (pinskerSecond x) x := by
  have hd:=((((Real.hasDerivAt_log (ne_of_gt hx.1)).sub
    ((Real.hasDerivAt_log (show 1-x≠0 by linarith [hx.2])).comp x
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x)))).sub_const (Real.log q)).add_const
    (Real.log (1-q))).sub (((hasDerivAt_id x).sub_const q).const_mul 4)
  convert hd using 1
  · funext y
    dsimp [pinskerFirst]
  · dsimp [pinskerSecond]
    simp only [one_div]
    ring

theorem potential_second_nonnegative (x : ℝ) (hx : x∈Set.Ioo (0:ℝ) 1) :
    0 ≤ pinskerSecond x := by
  have h1:0<1-x:=by linarith [hx.2]
  have he:pinskerSecond x=(2*x-1)^2/(x*(1-x)) := by
    unfold pinskerSecond
    field_simp [ne_of_gt hx.1,ne_of_gt h1]
    ring
  rw [he]
  exact div_nonneg (sq_nonneg _) (mul_nonneg hx.1.le h1.le)

theorem potential_convex (q : ℝ) : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (pinskerPotential q) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f':=pinskerFirst q)
    (f'':=pinskerSecond) (convex_Icc 0 1) (potential_continuous q).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (potential_has_derivative q x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (potential_second_derivative q x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact potential_second_nonnegative x hx

theorem actual_binary_log_sum_lower (q x : ℝ) (hq : q∈Set.Ioo (0:ℝ) 1)
    (hx : x∈Set.Icc (0:ℝ) 1) :
    2*(x-q)^2 ≤ x*Real.log (x/q)+(1-x)*Real.log ((1-x)/(1-q)) := by
  have hd:HasDerivAt (pinskerPotential q) 0 q := by
    simpa [pinskerFirst] using potential_has_derivative q q hq
  have hm:(pinskerPotential q q) ≤ pinskerPotential q x := by
    have hi:q∈interior (Set.Icc (0:ℝ) 1) := by simpa only [interior_Icc] using hq
    have hh:derivWithin (pinskerPotential q) (Set.Ioi q) q=0 :=
      hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi q)
    exact (potential_convex q).isMinOn_of_rightDeriv_eq_zero hi hh hx
  have hz:pinskerPotential q q=0 := by unfold pinskerPotential;ring
  rw [hz] at hm
  have hex (a b : ℝ) (ha : 0≤a) (hb : 0<b) :
      a*Real.log (a/b)=a*Real.log a-a*Real.log b := by
    by_cases haz:a=0
    · simp [haz]
    · rw [Real.log_div haz (ne_of_gt hb)]
      ring
  rw [hex x q hx.1 hq.1,hex (1-x) (1-q) (by linarith [hx.2]) (by linarith [hq.2])]
  unfold pinskerPotential at hm
  linarith

theorem actual_binary_pinsker_interior (p q : unitInterval)
    (hq : (q:ℝ)∈Set.Ioo (0:ℝ) 1) :
    2*totalVariation (costLaw p) (costLaw q)^2 ≤
      (klDiv (costLaw p).toMeasure (costLaw q).toMeasure).toReal := by
  rw [actual_binary_total_variation,actual_support_kl_sum _ _
    (by
      intro i _
      fin_cases i
      · change ENNReal.ofReal (1-(q:ℝ))≠0
        exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith [hq.2])
      · change ENNReal.ofReal (q:ℝ)≠0
        exact ENNReal.ofReal_ne_zero_iff.mpr hq.1)]
  simp only [costLaw,PMF.ofFintype_apply,Fin.sum_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Fin.sum_univ_zero,add_zero,
    ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2),ENNReal.toReal_ofReal p.2.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr q.2.2),ENNReal.toReal_ofReal q.2.1]
  rw [sq_abs]
  have h:=actual_binary_log_sum_lower (q:ℝ) (p:ℝ) hq p.2
  linarith

theorem actual_binary_pinsker (p q : unitInterval) :
    ENNReal.ofReal (2*totalVariation (costLaw p) (costLaw q)^2) ≤
      klDiv (costLaw p).toMeasure (costLaw q).toMeasure := by
  by_cases hq0:(q:ℝ)=0
  · by_cases hp0:(p:ℝ)=0
    · have he:p=q:=Subtype.ext (hp0.trans hq0.symm)
      subst p
      simp [actual_binary_total_variation]
    · rw [SafeLearning.CompleteAppliedFiniteKL.actual_missing_support_infinite_kl _ _ 1
        (by
          change ENNReal.ofReal (p:ℝ)≠0
          exact ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne p.2.1 (Ne.symm hp0)))
        (by change ENNReal.ofReal (q:ℝ)=0;simp [hq0])]
      exact le_top
  · by_cases hq1:(q:ℝ)=1
    · by_cases hp1:(p:ℝ)=1
      · have he:p=q:=Subtype.ext (hp1.trans hq1.symm)
        subst p
        simp [actual_binary_total_variation]
      · rw [SafeLearning.CompleteAppliedFiniteKL.actual_missing_support_infinite_kl _ _ 0
          (by
            change ENNReal.ofReal (1-(p:ℝ))≠0
            exact ENNReal.ofReal_ne_zero_iff.mpr
              (by have h:=lt_of_le_of_ne p.2.2 hp1;linarith))
          (by change ENNReal.ofReal (1-(q:ℝ))=0;simp [hq1])]
        exact le_top
    · have hq:(q:ℝ)∈Set.Ioo (0:ℝ) 1 :=
        ⟨lt_of_le_of_ne q.2.1 (Ne.symm hq0),lt_of_le_of_ne q.2.2 hq1⟩
      have hs:∀ i,(costLaw p) i≠0→(costLaw q) i≠0 := by
        intro i _
        fin_cases i
        · change ENNReal.ofReal (1-(q:ℝ))≠0
          exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith [hq.2])
        · change ENNReal.ofReal (q:ℝ)≠0
          exact ENNReal.ofReal_ne_zero_iff.mpr hq.1
      have hac:=(actual_support_absolute_continuity _ _).mpr hs
      have hf:=klDiv_ne_top hac Integrable.of_finite
      calc
        _≤ENNReal.ofReal (klDiv (costLaw p).toMeasure (costLaw q).toMeasure).toReal :=
          ENNReal.ofReal_le_ofReal (actual_binary_pinsker_interior p q hq)
        _=_:=ENNReal.ofReal_toReal hf

end SafeLearning.CompleteAppliedBinaryPinsker
