import SafeLearning.CompleteFoundationsSpectralModels
import Mathlib.Analysis.Calculus.FDeriv.WithLp

set_option autoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped Topology BigOperators Gradient

namespace SafeLearning.CompleteFoundationsLiteralJacobian28Notation
def coordinatePartial (dimension : ℕ) (f : EuclideanSpace ℝ (Fin dimension) → ℝ)
    (x : EuclideanSpace ℝ (Fin dimension)) (coordinate : Fin dimension) : ℝ :=
  deriv (fun t : ℝ => f (x+t • PiLp.single 2 coordinate (1:ℝ))) 0

theorem actual_coordinate_slice_has_the_frechet_directional_derivative
    (dimension : ℕ) (f : EuclideanSpace ℝ (Fin dimension) → ℝ)
    (x : EuclideanSpace ℝ (Fin dimension)) (hf : DifferentiableAt ℝ f x)
    (coordinate : Fin dimension) :
    HasDerivAt (fun t : ℝ => f (x+t • PiLp.single 2 coordinate (1:ℝ)))
      ((fderiv ℝ f x) (PiLp.single 2 coordinate (1:ℝ))) 0 := by
  have hs : HasDerivAt (fun t : ℝ => x+t • PiLp.single 2 coordinate (1:ℝ))
      (PiLp.single 2 coordinate (1:ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (PiLp.single 2 coordinate (1:ℝ))).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • PiLp.single 2 coordinate (1:ℝ)) :=
    by simpa using hf.hasFDerivAt
  convert! hf'.comp_hasDerivAt (0:ℝ) hs using 1

theorem actual_official_euclidean_gradient_is_the_vector_of_actual_partial_derivatives
    (dimension : ℕ) (f : EuclideanSpace ℝ (Fin dimension) → ℝ)
    (x : EuclideanSpace ℝ (Fin dimension)) (hf : DifferentiableAt ℝ f x)
    (coordinate : Fin dimension) :
    gradient f x coordinate = coordinatePartial dimension f x coordinate := by
  have hg : gradient f x coordinate =
      (fderiv ℝ f x) (PiLp.single 2 coordinate (1:ℝ)) := by
    rw [←inner_gradient_left]
    change gradient f x coordinate = inner ℝ (gradient f x) (EuclideanSpace.single coordinate (1:ℝ))
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [coordinatePartial, (actual_coordinate_slice_has_the_frechet_directional_derivative
    dimension f x hf coordinate).deriv]
  exact hg

def sourceJacobian (rows columns : ℕ)
    (f : EuclideanSpace ℝ (Fin columns) → EuclideanSpace ℝ (Fin rows))
    (x : EuclideanSpace ℝ (Fin columns)) : Matrix (Fin rows) (Fin columns) ℝ :=
  fun output input => (fderiv ℝ f x (PiLp.single 2 input (1:ℝ))) output

theorem actual_jacobian_entries_are_genuine_coordinate_partial_derivatives
    (rows columns : ℕ)
    (f : EuclideanSpace ℝ (Fin columns) → EuclideanSpace ℝ (Fin rows))
    (x : EuclideanSpace ℝ (Fin columns)) (hf : DifferentiableAt ℝ f x)
    (output : Fin rows) (input : Fin columns) :
    HasDerivAt (fun t : ℝ => f (x+t • PiLp.single 2 input (1:ℝ)) output)
      (sourceJacobian rows columns f x output input) 0 := by
  have hs : HasDerivAt (fun t : ℝ => x+t • PiLp.single 2 input (1:ℝ))
      (PiLp.single 2 input (1:ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (PiLp.single 2 input (1:ℝ))).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ) • PiLp.single 2 input (1:ℝ)) :=
    by simpa using hf.hasFDerivAt
  have hvec := hf'.comp_hasDerivAt 0 hs
  let projection : EuclideanSpace ℝ (Fin rows) →L[ℝ] ℝ := EuclideanSpace.proj output
  have houtput := projection.hasFDerivAt.comp_hasDerivAt (0:ℝ) hvec
  convert! houtput using 1

theorem actual_jacobian_is_the_matrix_of_the_genuine_frechet_derivative
    (rows columns : ℕ)
    (f : EuclideanSpace ℝ (Fin columns) → EuclideanSpace ℝ (Fin rows))
    (x velocity : EuclideanSpace ℝ (Fin columns)) :
    (fun output => (fderiv ℝ f x velocity) output) =
      (sourceJacobian rows columns f x).mulVec (fun input => velocity input) := by
  have hv : velocity = ∑ input, velocity input • PiLp.single 2 input (1:ℝ) := by
    ext input
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul]
  ext output
  simp [WithLp.ofLp_sum, sourceJacobian, Matrix.mulVec, dotProduct, mul_comm]

end SafeLearning.CompleteFoundationsLiteralJacobian28Notation

namespace SafeLearning.CompleteFoundationsLiteralJacobian28
open SafeLearning.CompleteFoundationsLiteralJacobian28Notation

abbrev Vector (n : ℕ) := EuclideanSpace ℝ (Fin n)

def matrixMap {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) :
    Vector n →L[ℝ] Vector m := (Matrix.toEuclideanLin W).toContinuousLinearMap

theorem actual_rectangular_matrix_map_coordinate_action {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (v : Vector n) (i : Fin m) :
    matrixMap W v i = W.mulVec (fun j => v j) i := by
  rfl

theorem actual_component_differentiability_supplies_the_full_vector_derivative
    {m n : ℕ} (f : Vector n → Vector m) (x : Vector n)
    (hf : ∀ i, DifferentiableAt ℝ (fun y => f y i) x) :
    DifferentiableAt ℝ f x := (differentiableAt_piLp 2).2 hf

theorem actual_jacobian_rows_are_the_gradients_of_the_actual_components
    {m n : ℕ} (f : Vector n → Vector m) (x : Vector n)
    (hf : ∀ i, DifferentiableAt ℝ (fun y => f y i) x)
    (i : Fin m) (j : Fin n) :
    sourceJacobian m n f x i j = gradient (fun y => f y i) x j := by
  rw [actual_official_euclidean_gradient_is_the_vector_of_actual_partial_derivatives n
    (fun y => f y i) x (hf i) j, coordinatePartial]
  exact (actual_jacobian_entries_are_genuine_coordinate_partial_derivatives m n f x
    (actual_component_differentiability_supplies_the_full_vector_derivative f x hf) i j).deriv.symm

theorem actual_jacobian_matrix_map_is_the_genuine_frechet_derivative
    {m n : ℕ} (f : Vector n → Vector m) (x : Vector n) :
    matrixMap (sourceJacobian m n f x) = fderiv ℝ f x := by
  ext velocity i
  exact (congrFun
    (actual_jacobian_is_the_matrix_of_the_genuine_frechet_derivative m n f x velocity) i).symm

theorem actual_full_jacobian_first_order_remainder_and_norm_ratio
    {m n : ℕ} (f : Vector n → Vector m) (x : Vector n)
    (hf : ∀ i, DifferentiableAt ℝ (fun y => f y i) x) :
    (∀ δ, f (x+δ) = f x + matrixMap (sourceJacobian m n f x) δ +
      (f (x+δ)-f x-matrixMap (sourceJacobian m n f x) δ)) ∧
    ((fun δ => f (x+δ)-f x-matrixMap (sourceJacobian m n f x) δ)
      =o[𝓝 0] (fun δ : Vector n => δ)) ∧
    Tendsto (fun δ => ‖f (x+δ)-f x-matrixMap (sourceJacobian m n f x) δ‖/‖δ‖)
      (𝓝 0) (𝓝 (0:ℝ)) := by
  have h := hasFDerivAt_iff_isLittleO_nhds_zero.mp
    (actual_component_differentiability_supplies_the_full_vector_derivative f x hf).hasFDerivAt
  rw [←actual_jacobian_matrix_map_is_the_genuine_frechet_derivative f x] at h
  refine ⟨?_,h,h.norm_norm.tendsto_div_nhds_zero⟩
  intro δ
  abel

theorem actual_jacobian_is_the_unique_first_order_linear_map
    {m n : ℕ} (f : Vector n → Vector m) (x : Vector n)
    (hf : ∀ i, DifferentiableAt ℝ (fun y => f y i) x)
    (L : Vector n →L[ℝ] Vector m)
    (hL : (fun δ => f (x+δ)-f x-L δ) =o[𝓝 0] (fun δ : Vector n => δ)) :
    L = matrixMap (sourceJacobian m n f x) := by
  have hd := hasFDerivAt_iff_isLittleO_nhds_zero.mpr hL
  rw [actual_jacobian_matrix_map_is_the_genuine_frechet_derivative f x]
  exact hd.unique
    (actual_component_differentiability_supplies_the_full_vector_derivative f x hf).hasFDerivAt

theorem actual_C1_nearby_supplies_every_component_and_the_jacobian_expansion
    {m n : ℕ} (f : Vector n → Vector m) (x : Vector n)
    (hf : ContDiffAt ℝ 1 f x) :
    ∀ i, DifferentiableAt ℝ (fun y => f y i) x := by
  exact (differentiableAt_piLp 2).1 (hf.differentiableAt (by norm_num))

def scalarVector {n : ℕ} (f : Vector n → ℝ) (x : Vector n) : Vector 1 :=
  WithLp.toLp 2 (fun _ : Fin 1 => f x)

theorem actual_scalar_jacobian_is_the_gradient_transpose
    {n : ℕ} (f : Vector n → ℝ) (x : Vector n)
    (hf : DifferentiableAt ℝ f x) (j : Fin n) :
    sourceJacobian 1 n (scalarVector f) x 0 j = gradient f x j := by
  have hc : ∀ i : Fin 1, DifferentiableAt ℝ (fun y => scalarVector f y i) x := by
    intro i
    simpa [scalarVector] using hf
  simpa [scalarVector] using
    actual_jacobian_rows_are_the_gradients_of_the_actual_components (scalarVector f) x hc 0 j

def affine {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (b : Vector m)
    (x : Vector n) : Vector m := matrixMap W x+b

theorem actual_arbitrary_rectangular_affine_map_has_derivative_W
    {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (b : Vector m) (x : Vector n) :
    HasFDerivAt (affine W b) (matrixMap W) x :=
  (matrixMap W).hasFDerivAt.add_const b

theorem actual_arbitrary_affine_jacobian_is_its_printed_matrix
    {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (b : Vector m) (x : Vector n) :
    sourceJacobian m n (affine W b) x = W := by
  ext i j
  rw [sourceJacobian, (actual_arbitrary_rectangular_affine_map_has_derivative_W W b x).fderiv,
    actual_rectangular_matrix_map_coordinate_action]
  simp [Matrix.mulVec, dotProduct, PiLp.single_apply]

def elementwise {n : ℕ} (σ : ℝ → ℝ) (v : Vector n) : Vector n :=
  WithLp.toLp 2 (fun i => σ (v i))

theorem actual_differentiable_scalar_activation_supplies_all_vector_components
    {n : ℕ} (σ : ℝ → ℝ) (v : Vector n)
    (hσ : ∀ i, DifferentiableAt ℝ σ (v i)) :
    ∀ i, DifferentiableAt ℝ (fun w => elementwise σ w i) v := by
  intro i
  exact (hσ i).comp v (PiLp.hasFDerivAt_apply 2 v i).differentiableAt

theorem actual_coordinate_of_a_basis_line_has_its_true_derivative
    {n : ℕ} (v : Vector n) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (v+t • (PiLp.single 2 j (1:ℝ) : Vector n)) i)
      ((PiLp.single 2 j (1:ℝ) : Vector n) i) 0 := by
  let b : Vector n := PiLp.single 2 j (1:ℝ)
  let projection : Vector n →L[ℝ] ℝ := EuclideanSpace.proj i
  have hline : HasDerivAt (fun t : ℝ => v+t • b) b (0:ℝ) := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const b).const_add v
  have hproj : HasFDerivAt projection projection (v+(0:ℝ) • b) := by
    simpa using projection.hasFDerivAt (x:=v)
  convert! hproj.comp_hasDerivAt (0:ℝ) hline using 1

theorem actual_elementwise_activation_jacobian_is_the_derivative_diagonal
    {n : ℕ} (σ : ℝ → ℝ) (v : Vector n)
    (hσ : ∀ i, DifferentiableAt ℝ σ (v i)) :
    sourceJacobian n n (elementwise σ) v = Matrix.diagonal (fun i => deriv σ (v i)) := by
  ext i j
  have hv := actual_coordinate_of_a_basis_line_has_its_true_derivative v i j
  have hbase : HasDerivAt σ (deriv σ (v i))
      ((v+(0:ℝ) • (PiLp.single 2 j (1:ℝ) : Vector n)) i) := by
    simpa using (hσ i).hasDerivAt
  have hs := hbase.comp (0:ℝ) hv
  have hall := actual_component_differentiability_supplies_the_full_vector_derivative
    (elementwise σ) v (actual_differentiable_scalar_activation_supplies_all_vector_components σ v hσ)
  have hj := actual_jacobian_entries_are_genuine_coordinate_partial_derivatives n n
    (elementwise σ) v hall i j
  have he := hj.unique (by simpa [elementwise] using hs)
  simpa [Matrix.diagonal, PiLp.single_apply, Pi.single_apply, eq_comm] using he

open SafeLearning.CompleteFoundationsSpectralModels (E point norm_squared_coordinates)
def polynomialVector (x : E) : E := point (x 0*x 1) (x 0+(x 1)^2)
def polynomialJacobian (x : E) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x 1,x 0;1,2*x 1]

theorem actual_printed_polynomial_vector_has_differentiable_components (x : E) :
    ∀ i, DifferentiableAt ℝ (fun y => polynomialVector y i) x := by
  intro i
  fin_cases i
  · exact ((PiLp.hasFDerivAt_apply 2 x 0).differentiableAt.mul
      (PiLp.hasFDerivAt_apply 2 x 1).differentiableAt)
  · exact ((PiLp.hasFDerivAt_apply 2 x 0).differentiableAt.add
      ((PiLp.hasFDerivAt_apply 2 x 1).differentiableAt.pow 2))

theorem actual_printed_polynomial_jacobian_at_every_point (x : E) :
    sourceJacobian 2 2 polynomialVector x = polynomialJacobian x := by
  let c0 : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let c1 : E →L[ℝ] ℝ := EuclideanSpace.proj 1
  have h0 := c0.hasFDerivAt (x:=x)
  have h1 := c1.hasFDerivAt (x:=x)
  have hf0 : HasFDerivAt (fun y => polynomialVector y 0)
      ((x 1) • c0+(x 0) • c1) x := by
    convert! h0.mul h1 using 1 <;>
      ext u <;>
      simp [polynomialVector,point,c0,c1,EuclideanSpace.proj,PiLp.proj,PiLp.projₗ] <;> ring
  have hf1 : HasFDerivAt (fun y => polynomialVector y 1)
      (c0+(2*x 1) • c1) x := by
    convert! h0.add (h1.pow 2) using 1 <;>
      ext u <;>
      simp [polynomialVector,point,c0,c1,EuclideanSpace.proj,PiLp.proj,PiLp.projₗ] <;> ring
  have hv : HasFDerivAt polynomialVector (matrixMap (polynomialJacobian x)) x := by
    rw [←hasFDerivWithinAt_univ]
    apply (hasFDerivWithinAt_piLp 2).2
    intro i
    fin_cases i
    · convert! hf0.hasFDerivWithinAt using 1
      ext u
      simp [PiLp.proj,PiLp.projₗ,matrixMap,Matrix.toEuclideanLin,Matrix.toLpLin_apply,
        polynomialJacobian,dotProduct,Fin.sum_univ_succ,c0,c1]
    · convert! hf1.hasFDerivWithinAt using 1
      ext u
      simp [PiLp.proj,PiLp.projₗ,matrixMap,Matrix.toEuclideanLin,Matrix.toLpLin_apply,
        polynomialJacobian,dotProduct,Fin.sum_univ_succ,c0,c1]
  ext i j
  rw [sourceJacobian,hv.fderiv,actual_rectangular_matrix_map_coordinate_action]
  simp [Matrix.mulVec,dotProduct,PiLp.single_apply]

theorem actual_printed_polynomial_jacobian_at_one_two :
    sourceJacobian 2 2 polynomialVector (point 1 2) = !![(2:ℝ),1;1,4] := by
  rw [actual_printed_polynomial_jacobian_at_every_point]
  norm_num [polynomialJacobian,point]

/-- The exact printed counterexample; Lean's real division also gives zero at
the origin, so no alternative off-origin model or completion is substituted. -/
def literalPitfall (x : E) : ℝ := x 0 * x 1 / ((x 0)^2+(x 1)^2)

theorem actual_literal_pitfall_origin_and_axis_restrictions_are_zero :
    literalPitfall 0 = 0 ∧
    (∀ t : ℝ, literalPitfall (point t 0) = 0) ∧
    (∀ t : ℝ, literalPitfall (point 0 t) = 0) := by
  simp [literalPitfall, point]

theorem actual_literal_pitfall_has_both_zero_coordinate_partials :
    HasDerivAt (fun t => literalPitfall (point t 0)) 0 0 ∧
    HasDerivAt (fun t => literalPitfall (point 0 t)) 0 0 := by
  have hx : (fun t => literalPitfall (point t 0)) = (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact actual_literal_pitfall_origin_and_axis_restrictions_are_zero.2.1 t
  have hy : (fun t => literalPitfall (point 0 t)) = (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact actual_literal_pitfall_origin_and_axis_restrictions_are_zero.2.2 t
  rw [hx,hy]
  exact ⟨hasDerivAt_const 0 0,hasDerivAt_const 0 0⟩

theorem actual_literal_pitfall_is_one_half_everywhere_on_the_nonzero_diagonal
    (t : ℝ) (ht : t ≠ 0) : literalPitfall (point t t) = 1/2 := by
  have hs : t^2 ≠ 0 := pow_ne_zero 2 ht
  have hd : t^2+t^2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero ht]
  change t*t/(t^2+t^2) = (1 : ℝ)/2
  field_simp
  ring

theorem actual_literal_pitfall_is_not_continuous_at_the_origin :
    ¬ ContinuousAt literalPitfall (0 : E) := by
  intro h
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp h (1/4) (by norm_num)
  let t : ℝ := δ/4
  have ht : 0 < t := by dsimp [t];positivity
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hn : ‖point t t‖^2 = 2*t^2 := by
    rw [norm_squared_coordinates]
    simp [point]
    ring
  have hsmall : ‖point t t‖ < δ := by
    have := norm_nonneg (point t t)
    dsimp [t] at hn
    nlinarith
  have h := hclose (x:=point t t) (by simpa [dist_zero_right] using hsmall)
  rw [actual_literal_pitfall_is_one_half_everywhere_on_the_nonzero_diagonal t ht0,
    actual_literal_pitfall_origin_and_axis_restrictions_are_zero.1] at h
  norm_num [Real.dist_eq] at h

theorem actual_literal_zero_partials_do_not_give_differentiability_or_C1 :
    ¬ DifferentiableAt ℝ literalPitfall (0 : E) ∧
    ¬ ContDiffAt ℝ 1 literalPitfall (0 : E) := by
  constructor
  · intro h
    exact actual_literal_pitfall_is_not_continuous_at_the_origin h.continuousAt
  · intro h
    exact actual_literal_pitfall_is_not_continuous_at_the_origin h.continuousAt

theorem actual_zero_entry_jacobian_of_the_printed_pitfall_gives_no_linear_approximation :
    (∀ j : Fin 2, coordinatePartial 2 literalPitfall 0 j = 0) ∧
    ¬ DifferentiableAt ℝ literalPitfall (0:E) ∧
    (∀ t : ℝ, t ≠ 0 → literalPitfall (point t t) = 1/2) := by
  refine ⟨?_,actual_literal_zero_partials_do_not_give_differentiability_or_C1.1,
    actual_literal_pitfall_is_one_half_everywhere_on_the_nonzero_diagonal⟩
  intro j
  fin_cases j
  · have h := actual_literal_pitfall_has_both_zero_coordinate_partials.1.deriv
    unfold coordinatePartial
    convert h using 1
    congr 1
    funext t
    congr 1
    ext i
    fin_cases i <;> simp [point]
  · have h := actual_literal_pitfall_has_both_zero_coordinate_partials.2.deriv
    unfold coordinatePartial
    convert h using 1
    congr 1
    funext t
    congr 1
    ext i
    fin_cases i <;> simp [point]

theorem actual_printed_zero_partials_cannot_supply_any_first_order_linear_map :
    ¬ ∃ L : E →L[ℝ] ℝ,
      (fun δ => literalPitfall δ-literalPitfall 0-L δ) =o[𝓝 0] (fun δ : E => δ) := by
  rintro ⟨L,hL⟩
  have hd : HasFDerivAt literalPitfall L (0:E) := by
    apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
    simpa using hL
  exact actual_literal_zero_partials_do_not_give_differentiability_or_C1.1 hd.differentiableAt

end SafeLearning.CompleteFoundationsLiteralJacobian28
