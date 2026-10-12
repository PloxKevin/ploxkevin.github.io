import Mathlib
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteCoreProjectedDualDrift29
variable {m : ℕ}
def step (eta : ℝ) (l g : Fin m → ℝ) (i : Fin m) : ℝ := max 0 (l i - eta * g i)
def energy (l : Fin m → ℝ) : ℝ := ∑ i, (l i)^2
def pairing (l g : Fin m → ℝ) : ℝ := ∑ i, l i*g i
def multiplier (eta : ℝ) (l0 : Fin m → ℝ) (g : ℕ → Fin m → ℝ) : ℕ → Fin m → ℝ
 | 0 => l0
 | n+1 => step eta (multiplier eta l0 g n) (g n)

theorem projected_scalar_square_bound (a : ℝ) : (max 0 a)^2 ≤ a^2 := by
 by_cases ha : 0 ≤ a
 · simp [max_eq_right ha]
 · rw [max_eq_left (le_of_not_ge ha)]
   simpa using sq_nonneg a

theorem actual_projected_step_energy_bound (eta : ℝ) (l g : Fin m → ℝ) :
 energy (step eta l g) ≤ energy l + eta^2*energy g - 2*eta*pairing l g := by
 calc
  energy (step eta l g) ≤ ∑ i, (l i-eta*g i)^2 := by
   exact Finset.sum_le_sum (fun i _ => projected_scalar_square_bound _)
  _ = energy l + eta^2*energy g - 2*eta*pairing l g := by
   simp only [energy,pairing,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
   congr 1
   ext i
   ring

theorem actual_all_multiplier_coordinates_nonnegative (eta : ℝ) (l0 : Fin m → ℝ)
 (h0 : ∀ i, 0 ≤ l0 i) (g : ℕ → Fin m → ℝ) (n : ℕ) (i : Fin m) :
 0 ≤ multiplier eta l0 g n i := by
 cases n with
 | zero => exact h0 i
 | succ n => exact le_max_left _ _

theorem actual_projected_dual_cumulative_deficit (eta : ℝ) (l0 : Fin m → ℝ)
 (g : ℕ → Fin m → ℝ) (N : ℕ) (i : Fin m) :
 l0 i-eta*(∑ n ∈ Finset.range N,g n i) ≤ multiplier eta l0 g N i := by
 induction N with
 | zero => simp [multiplier]
 | succ N ih =>
  rw [Finset.sum_range_succ,multiplier]
  have h : multiplier eta l0 g N i-eta*g N i ≤ step eta (multiplier eta l0 g N) (g N) i := le_max_right _ _
  linarith

theorem actual_energy_telescope (eta B : ℝ) (l0 : Fin m → ℝ)
 (g : ℕ → Fin m → ℝ) (hB : ∀ n, energy (g n) ≤ B^2) (N : ℕ) :
 energy (multiplier eta l0 g N) ≤ energy l0 + (N:ℝ)*eta^2*B^2-
 2*eta*(∑ n ∈ Finset.range N,pairing (multiplier eta l0 g n) (g n)) := by
 induction N with
 | zero => simp [multiplier]
 | succ N ih =>
  rw [Finset.sum_range_succ,multiplier]
  have hs:=actual_projected_step_energy_bound eta (multiplier eta l0 g N) (g N)
  have hb:=mul_le_mul_of_nonneg_left (hB N) (sq_nonneg eta)
  push_cast
  nlinarith

theorem actual_finite_horizon_complementary_slackness (eta B : ℝ) (heta : 0<eta)
 (l0 : Fin m → ℝ) (g : ℕ → Fin m → ℝ) (hB : ∀ n, energy (g n) ≤ B^2)
 (N : ℕ) (hN : 0<N) :
 (∑ n ∈ Finset.range N,pairing (multiplier eta l0 g n) (g n))/(N:ℝ) ≤
 energy l0/(2*eta*(N:ℝ))+eta*B^2/2 := by
 have hn : (0:ℝ)<N := by exact_mod_cast hN
 have he:=actual_energy_telescope eta B l0 g hB N
 have hz : 0 ≤ energy (multiplier eta l0 g N) := Finset.sum_nonneg (fun i _ => sq_nonneg _)
 have hh : 0<2*eta*(N:ℝ) := by positivity
 apply (div_le_iff₀ hn).mpr
 have h : (∑ n ∈ Finset.range N,pairing (multiplier eta l0 g n) (g n)) ≤
 energy l0/(2*eta) + (N:ℝ)*eta*B^2/2 := by
  have hc : (∑ n ∈ Finset.range N,pairing (multiplier eta l0 g n) (g n))*(2*eta) ≤ energy l0+(N:ℝ)*eta^2*B^2 := by nlinarith
  have hv := (le_div_iff₀ (show (0:ℝ)<2*eta by positivity)).mpr hc
  convert hv using 1 <;> field_simp <;> ring
 have eq : (energy l0/(2*eta*(N:ℝ))+eta*B^2/2)*(N:ℝ)=energy l0/(2*eta)+(N:ℝ)*eta*B^2/2 := by
  field_simp <;> ring
 rw [eq]
 exact h

theorem actual_slater_maximizer_pairing_drift (C rChosen rSlater upper : ℝ)
 (l gChosen gSlater : Fin m → ℝ) (hl : ∀ i,0≤l i)
 (hs : ∀ i,C≤gSlater i) (hr : rChosen≤upper)
 (hmax : rSlater+pairing l gSlater ≤ rChosen+pairing l gChosen) :
 C*(∑ i,l i)-(upper-rSlater) ≤ pairing l gChosen := by
 have hsum : C*(∑ i,l i) ≤ pairing l gSlater := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  nlinarith [hs i,hl i]
 linarith
end SafeLearning.CompleteCoreProjectedDualDrift29
