import SafeLearning.CompleteModulesTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set BigOperators
namespace SafeLearning.CompleteModulesGoSafeGridScaling

def actualCellCenter (h : ℝ) {n : ℕ} (i : Fin n) : ℝ := ((i.val:ℝ)+1/2)*h
def actualGridPoint (h : ℝ) {n s : ℕ} (index : Fin s → Fin n) : Fin s → ℝ :=
  fun i => actualCellCenter h (index i)
def actualL1Distance {s : ℕ} (x y : Fin s → ℝ) : ℝ := ∑ i, |x i-y i|
def actualBox (n s : ℕ) (h : ℝ) : Set (Fin s → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ (n:ℝ)*h}
def actualGridPoints (n s : ℕ) (h : ℝ) : Finset (Fin s → ℝ) :=
  Finset.univ.image (actualGridPoint h : (Fin s → Fin n) → (Fin s → ℝ))

theorem actual_scalar_cell_center_quantization_exists
    (n : ℕ) (hn : 0 < n) (h x : ℝ) (hh : 0 < h)
    (hx : 0 ≤ x) (hxn : x ≤ (n:ℝ)*h) :
    ∃ i : Fin n, |x-actualCellCenter h i| ≤ h/2 := by
  by_cases hlt : x < (n:ℝ)*h
  · have hquot : 0 ≤ x/h := div_nonneg hx hh.le
    have hqbound : x/h < (n:ℝ) := (div_lt_iff₀ hh).mpr hlt
    have hi : Nat.floor (x/h) < n := (Nat.floor_lt hquot).mpr hqbound
    refine ⟨⟨Nat.floor (x/h),hi⟩,?_⟩
    have hlo := Nat.floor_le hquot
    have hup := Nat.lt_floor_add_one (x/h)
    have hlo' : (Nat.floor (x/h):ℝ)*h ≤ x := by
      simpa [div_mul_cancel₀ x hh.ne'] using (mul_le_mul_of_nonneg_right hlo hh.le)
    have hup' : x < ((Nat.floor (x/h):ℝ)+1)*h := by
      simpa [div_mul_cancel₀ x hh.ne'] using (mul_lt_mul_of_pos_right hup hh)
    rw [abs_le]
    simp only [actualCellCenter]
    constructor <;> linarith
  · have hxend : x=(n:ℝ)*h := le_antisymm hxn (le_of_not_gt hlt)
    have hi : n-1<n := by omega
    have hcast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
    refine ⟨⟨n-1,hi⟩,?_⟩
    simp only [actualCellCenter,hxend,hcast]
    have heq : (n:ℝ)*h-((n:ℝ)-1+1/2)*h=h/2 := by ring
    rw [heq,abs_of_nonneg (by linarith)]

theorem actual_grid_has_exactly_n_to_the_state_dimension_distinct_cell_centers
    (n s : ℕ) (h : ℝ) (hh : 0 < h) :
    (actualGridPoints n s h).card=n^s := by
  have hinj : Function.Injective (actualGridPoint h : (Fin s → Fin n) → (Fin s → ℝ)) := by
    intro a b heq
    funext i
    apply Fin.ext
    have hi := congrFun heq i
    simp only [actualGridPoint,actualCellCenter] at hi
    have hicast : (a i).val=(b i).val := by exact_mod_cast (by nlinarith : ((a i).val:ℝ)=((b i).val:ℝ))
    exact hicast
  rw [actualGridPoints,Finset.card_image_of_injective _ hinj]
  simp

theorem actual_every_box_point_has_a_cell_center_with_l1_error_at_most_shared_half_spacing
    (n s : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 < h)
    (x : Fin s → ℝ) (hx : x ∈ actualBox n s h) :
    ∃ index : Fin s → Fin n, actualL1Distance x (actualGridPoint h index) ≤ (s:ℝ)*h/2 := by
  have hex : ∀ i : Fin s, ∃ j : Fin n, |x i-actualCellCenter h j| ≤ h/2 :=
    fun i => actual_scalar_cell_center_quantization_exists n hn h (x i) hh (hx i).1 (hx i).2
  choose index hi using hex
  refine ⟨index,?_⟩
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hi i)
  simpa [actualL1Distance,actualGridPoint,Finset.sum_const,mul_div_assoc] using hsum

theorem actual_zero_corner_has_l1_distance_at_least_shared_half_spacing_to_every_grid_point
    (n s : ℕ) (h : ℝ) (hh : 0 < h) (index : Fin s → Fin n) :
    (s:ℝ)*h/2 ≤ actualL1Distance (fun _ => 0) (actualGridPoint h index) := by
  have hi : ∀ i : Fin s, h/2 ≤ |0-actualCellCenter h (index i)| := by
    intro i
    have hn : 0 ≤ ((index i).val:ℝ) := Nat.cast_nonneg _
    simp only [actualCellCenter,zero_sub,abs_neg]
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hi i)
  simpa [actualL1Distance,actualGridPoint,Finset.sum_const,mul_div_assoc] using hsum

theorem actual_shared_half_spacing_is_the_least_uniform_l1_covering_radius
    (n s : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 < h) :
    IsLeast {radius : ℝ | ∀ x ∈ actualBox n s h,
      ∃ index : Fin s → Fin n, actualL1Distance x (actualGridPoint h index) ≤ radius}
      ((s:ℝ)*h/2) := by
  constructor
  · intro x hx
    exact actual_every_box_point_has_a_cell_center_with_l1_error_at_most_shared_half_spacing n s hn h hh x hx
  · intro radius hr
    have hzero : (fun _ : Fin s => (0:ℝ)) ∈ actualBox n s h := by
      intro i
      constructor
      · rfl
      · positivity
    obtain ⟨index,hindex⟩ := hr (fun _ => 0) hzero
    exact (actual_zero_corner_has_l1_distance_at_least_shared_half_spacing_to_every_grid_point n s h hh index).trans hindex

theorem actual_shared_l1_tolerance_requires_spacing_at_most_two_mu_over_dimension
    (n s : ℕ) (hn : 0 < n) (hs : 0 < s) (h mu : ℝ) (hh : 0 < h) :
    (∀ x ∈ actualBox n s h, ∃ index : Fin s → Fin n,
      actualL1Distance x (actualGridPoint h index) ≤ mu) ↔ h ≤ 2*mu/(s:ℝ) := by
  have hmin := actual_shared_half_spacing_is_the_least_uniform_l1_covering_radius n s hn h hh
  have hsreal : 0 < (s:ℝ) := by exact_mod_cast hs
  constructor
  · intro ht
    have hbound := hmin.2 ht
    apply (le_div_iff₀ hsreal).mpr
    nlinarith
  · intro ht x hx
    obtain ⟨index,hi⟩ := hmin.1 x hx
    refine ⟨index,hi.trans ?_⟩
    have hbound := (le_div_iff₀ hsreal).mp ht
    nlinarith

theorem actual_source_candidate_and_endpoint_grid_counts :
    Fintype.card (Fin 625 × (Fin 2 → Fin 40))=1000000 ∧
      Fintype.card (Fin 625 × (Fin 6 → Fin 120))=1866240000000000 ∧
      Fintype.card (Fin 2 → Fin 41)=1681 ∧
      Fintype.card (Fin 6 → Fin 121)=3138428376721 := by norm_num

theorem actual_source_spacing_and_big_count_roundings :
    2*(1/20:ℝ)/2=1/20 ∧ 2/(1/20:ℝ)=40 ∧
      2*(1/20:ℝ)/6=1/60 ∧ 2/(1/60:ℝ)=120 ∧
      |(1/60:ℝ)-(167/10000)|<1/20000 ∧
      |(120^6:ℝ)-3*10^12|<(1/2:ℝ)*10^12 ∧
      |(625*120^6:ℝ)-(19/10)*10^15|<(1/20:ℝ)*10^15 ∧
      (1/60:ℝ)<1/20 ∧ (1/60:ℝ)≠(167/10000) := by norm_num

theorem actual_squared_euclidean_backup_multiplication_operation_indices_and_hardware_rate :
    Fintype.card (Fin 500 × Fin 6)=3000 ∧
      Fintype.card (Fin 100 × (Fin 500 × Fin 6))=300000 ∧
      ∀ s : ℕ, Fintype.card (Fin 500 × Fin s)=500*s := by norm_num

end SafeLearning.CompleteModulesGoSafeGridScaling
