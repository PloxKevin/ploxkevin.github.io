import SafeLearning.CompleteModulesGoSafeGridScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter BigOperators
namespace SafeLearning.CompleteModulesGoSafeGridFamilies
open SafeLearning.CompleteModulesGoSafeGridScaling

def actualEndpoint (h : ℝ) {n : ℕ} (i : Fin (n+1)) : ℝ := (i.val:ℝ)*h
def actualEndpointGridPoint (h : ℝ) {n s : ℕ} (index : Fin s → Fin (n+1)) : Fin s → ℝ :=
  fun i => actualEndpoint h (index i)
def actualEndpointGridPoints (n s : ℕ) (h : ℝ) : Finset (Fin s → ℝ) :=
  Finset.univ.image (actualEndpointGridPoint h : (Fin s → Fin (n+1)) → (Fin s → ℝ))

theorem actual_endpoint_grid_includes_both_box_endpoints (n : ℕ) (h : ℝ) :
    actualEndpoint h (0:Fin (n+1))=0 ∧ actualEndpoint h (Fin.last n)=(n:ℝ)*h := by
  simp [actualEndpoint]

theorem actual_endpoint_grid_has_exactly_n_plus_one_to_the_dimension_distinct_points
    (n s : ℕ) (h : ℝ) (hh : 0 < h) :
    (actualEndpointGridPoints n s h).card=(n+1)^s := by
  have hinj : Function.Injective (actualEndpointGridPoint h : (Fin s → Fin (n+1)) → (Fin s → ℝ)) := by
    intro a b hab
    funext i
    apply Fin.ext
    have hi := congrFun hab i
    simp only [actualEndpointGridPoint,actualEndpoint] at hi
    exact_mod_cast (by nlinarith : ((a i).val:ℝ)=((b i).val:ℝ))
  rw [actualEndpointGridPoints,Finset.card_image_of_injective _ hinj]
  simp

theorem actual_scalar_endpoint_grid_quantization_exists
    (n : ℕ) (hn : 0 < n) (h x : ℝ) (hh : 0 < h)
    (hx : 0 ≤ x) (hxn : x ≤ (n:ℝ)*h) :
    ∃ i : Fin (n+1), |x-actualEndpoint h i| ≤ h/2 := by
  obtain ⟨j,hj⟩ := actual_scalar_cell_center_quantization_exists n hn h x hh hx hxn
  have hb := abs_le.mp hj
  have hcast : (j.val:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast j.isLt
  by_cases hleft : x ≤ actualCellCenter h j
  · refine ⟨⟨j.val,by omega⟩,?_⟩
    rw [abs_le]
    simp only [actualEndpoint,actualCellCenter] at *
    constructor <;> linarith
  · refine ⟨⟨j.val+1,by omega⟩,?_⟩
    rw [abs_le]
    simp only [actualEndpoint,Nat.cast_add,Nat.cast_one,actualCellCenter] at *
    constructor <;> linarith

theorem actual_every_box_point_has_an_endpoint_grid_point_with_l1_error_at_most_shared_half_spacing
    (n s : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 < h)
    (x : Fin s → ℝ) (hx : x ∈ actualBox n s h) :
    ∃ index : Fin s → Fin (n+1), actualL1Distance x (actualEndpointGridPoint h index) ≤ (s:ℝ)*h/2 := by
  have hex : ∀ i : Fin s, ∃ j : Fin (n+1), |x i-actualEndpoint h j| ≤ h/2 :=
    fun i => actual_scalar_endpoint_grid_quantization_exists n hn h (x i) hh (hx i).1 (hx i).2
  choose index hi using hex
  refine ⟨index,?_⟩
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hi i)
  simpa [actualL1Distance,actualEndpointGridPoint,Finset.sum_const,mul_div_assoc] using hsum

theorem actual_endpoint_grid_shared_half_spacing_is_the_least_uniform_l1_covering_radius
    (n s : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 < h) :
    IsLeast {radius : ℝ | ∀ x ∈ actualBox n s h,
      ∃ index : Fin s → Fin (n+1), actualL1Distance x (actualEndpointGridPoint h index) ≤ radius}
      ((s:ℝ)*h/2) := by
  have hi : ∀ i : Fin (n+1), h/2 ≤ |h/2-actualEndpoint h i| := by
    intro i
    by_cases hz : i.val=0
    · simp [actualEndpoint,hz,abs_of_pos (by linarith : 0 < h/2)]
    · have hncast : (1:ℝ) ≤ (i.val:ℝ) := by exact_mod_cast (by omega : 1 ≤ i.val)
      unfold actualEndpoint
      rw [abs_of_nonpos (by nlinarith)]
      nlinarith
  constructor
  · intro x hx
    exact actual_every_box_point_has_an_endpoint_grid_point_with_l1_error_at_most_shared_half_spacing n s hn h hh x hx
  · intro radius hr
    have hbox : (fun _ : Fin s => h/2) ∈ actualBox n s h := by
      intro i
      have hncast : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      constructor <;> nlinarith
    obtain ⟨index,hindex⟩ := hr (fun _ => h/2) hbox
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hi (index i))
    have hlower : (s:ℝ)*h/2 ≤ actualL1Distance (fun _ => h/2) (actualEndpointGridPoint h index) := by
      simpa [actualL1Distance,actualEndpointGridPoint,Finset.sum_const,mul_div_assoc] using hsum
    exact hlower.trans hindex

theorem actual_fixed_axis_resolution_grows_exponentially_with_dimension
    (n : ℕ) (hn : 1 < n) :
    (∀ s : ℕ, n^(s+1)=n*n^s) ∧
      Tendsto (fun s : ℕ => (n:ℝ)^s) atTop atTop := by
  constructor
  · intro s
    rw [pow_succ,mul_comm]
  · exact tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hn)

theorem actual_finer_axis_resolution_families_are_bounded_below_by_a_genuine_exponential
    (resolution : ℕ → ℕ) (base : ℕ) (hbase : 1 < base)
    (hresolution : ∀ s : ℕ, base ≤ resolution s) :
    (∀ s : ℕ, base^s ≤ (resolution s)^s) ∧
      Tendsto (fun s : ℕ => (resolution s:ℝ)^s) atTop atTop := by
  constructor
  · intro s
    exact pow_le_pow_left' (hresolution s) s
  · apply tendsto_atTop_mono (fun s => ?_) (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hbase : (1:ℝ)<base))
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hresolution s) s

end SafeLearning.CompleteModulesGoSafeGridFamilies
