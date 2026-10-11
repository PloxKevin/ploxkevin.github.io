import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology Matrix.Norms.Operator
namespace SafeLearning.CompleteFoundationsTransientNeumann

theorem actual_power_decay_provides_a_strictly_contractive_block
    {R : Type*} [NormedRing R] (A : R)
    (hA : Tendsto (fun n : ℕ => A^n) atTop (𝓝 0)) :
    ∃ N : ℕ, 0 < N ∧ ‖A^N‖ < 1 := by
  have ht : Tendsto (fun n : ℕ => ‖A^n‖) atTop (𝓝 0) := by
    simpa using hA.norm
  have he : ∀ᶠ n : ℕ in atTop, ‖A^n‖ < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨N, hN, hlt⟩ := (he.and (eventually_gt_atTop 0)).exists
  exact ⟨N, hlt, hN⟩

theorem actual_power_decay_implies_absolute_summability_of_the_power_series
    {R : Type*} [NormedRing R] [CompleteSpace R] (A : R)
    (hA : Tendsto (fun n : ℕ => A^n) atTop (𝓝 0)) :
    Summable (fun n : ℕ => ‖A^n‖) := by
  obtain ⟨N,hN,hblock⟩ := actual_power_decay_provides_a_strictly_contractive_block A hA
  haveI : NeZero N := ⟨hN.ne'⟩
  have hr (r : Fin N) : Summable (fun k : ℕ => ‖A^(k*N+r.val)‖) := by
    have hg := (summable_norm_geometric_of_norm_lt_one hblock).mul_right ‖A^r.val‖
    apply hg.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    have he : A^(k*N+r.val)=(A^N)^k*A^r.val := by
      rw [pow_add, Nat.mul_comm k N, pow_mul]
    rw [he]
    exact norm_mul_le _ _
  have hp : Summable (fun p : Fin N × ℕ => ‖A^(p.2*N+p.1.val)‖) :=
    (summable_prod_of_nonneg
      (f := fun p : Fin N × ℕ => ‖A^(p.2*N+p.1.val)‖)
      (fun _ => norm_nonneg _)).mpr
      ⟨hr, (hasSum_fintype (fun r : Fin N => ∑' k : ℕ, ‖A^(k*N+r.val)‖)).summable⟩
  have hp' : Summable (fun p : ℕ × Fin N => ‖A^(p.1*N+p.2.val)‖) :=
    hp.comp_injective (Equiv.prodComm ℕ (Fin N)).injective
  exact (Nat.divModEquiv N).symm.summable_iff.mp hp'

theorem actual_power_decay_implies_a_true_unit_and_inverse_neumann_series
    {R : Type*} [NormedRing R] [CompleteSpace R] (A : R)
    (hA : Tendsto (fun n : ℕ => A^n) atTop (𝓝 0)) :
    IsUnit (1-A) ∧ HasSum (fun n : ℕ => A^n) (Ring.inverse (1-A)) ∧
    (1-A)*(∑' n : ℕ,A^n)=1 ∧ (∑' n : ℕ,A^n)*(1-A)=1 := by
  obtain ⟨N,_,hblock⟩ := actual_power_decay_provides_a_strictly_contractive_block A hA
  have huN : IsUnit (1-A^N) := isUnit_one_sub_of_norm_lt_one hblock
  have hl : (1-A)*(∑ n ∈ Finset.range N,A^n)=1-A^N := by
    have h := mul_geom_sum A N
    rw [sub_mul,one_mul] at h
    rw [sub_mul,one_mul]
    simpa only [neg_sub] using congrArg Neg.neg h
  have hr : (∑ n ∈ Finset.range N,A^n)*(1-A)=1-A^N := by
    simpa only [mul_sub,mul_one,neg_sub] using geom_sum_mul_neg A N
  have hc : Commute (1-A) (∑ n ∈ Finset.range N,A^n) := by
    change _=_
    rw [hl,hr]
  have hu : IsUnit (1-A) := (hc.isUnit_mul_iff.mp (hl.symm ▸ huN)).1
  have hs : Summable (fun n : ℕ => A^n) :=
    (actual_power_decay_implies_absolute_summability_of_the_power_series A hA).of_norm
  have hleft := hs.one_sub_mul_tsum_pow
  have hright := hs.tsum_pow_mul_one_sub
  have he : (∑' n : ℕ,A^n)=Ring.inverse (1-A) := by
    calc
      _=Ring.inverse (1-A)*((1-A)*(∑' n : ℕ,A^n)) := by
        rw [←mul_assoc,Ring.inverse_mul_cancel (1-A) hu,one_mul]
      _=Ring.inverse (1-A) := by rw [hleft,mul_one]
  exact ⟨hu,he ▸ hs.hasSum,hleft,hright⟩

variable {S : Type*} [Fintype S] [DecidableEq S]

local instance : TopologicalSpace (Matrix S S ℝ) :=
  (Matrix.linftyOpNormedRing (n:=S) (α:=ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem actual_finite_transient_matrix_power_decay_implies_its_literal_inverse_series
    (P : Matrix S S ℝ)
    (hP : Tendsto (fun n : ℕ => P^n) atTop (𝓝 0)) :
    IsUnit (1-P) ∧ HasSum (fun n : ℕ => P^n) ((1-P)⁻¹) ∧
    (∑' n : ℕ,P^n)=(1-P)⁻¹ := by
  have h := actual_power_decay_implies_a_true_unit_and_inverse_neumann_series P hP
  have hs : HasSum (fun n : ℕ => P^n) ((1-P)⁻¹) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using h.2.1
  exact ⟨h.1,hs,hs.tsum_eq⟩

end SafeLearning.CompleteFoundationsTransientNeumann
