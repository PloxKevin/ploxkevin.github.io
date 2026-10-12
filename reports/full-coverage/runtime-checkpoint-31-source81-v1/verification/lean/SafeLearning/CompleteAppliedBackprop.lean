import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedBackprop
open Filter
open scoped Topology

def neuron (w a b x : ℝ) : ℝ := w * max 0 (a * x + b)
def loss (w a b x y : ℝ) : ℝ := (neuron w a b x - y) ^ 2 / 2

theorem active_affine_relu_derivative (a b x : ℝ) (hactive : 0 < a * x + b) :
    HasDerivAt (fun z : ℝ => max 0 (a * z + b)) a x := by
  have hd : HasDerivAt (fun z : ℝ => a * z + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have hp : ∀ᶠ z in 𝓝 x, 0 < a * z + b :=
    hd.continuousAt.eventually (lt_mem_nhds hactive)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hp] with z hz
  exact max_eq_right hz.le

theorem squared_loss_chain (f : ℝ → ℝ) (derivative input target : ℝ)
    (hf : HasDerivAt f derivative input) :
    HasDerivAt (fun z => (f z - target) ^ 2 / 2)
      ((f input - target) * derivative) input := by
  convert (hf.sub_const target |>.pow 2 |>.div_const 2) using 1 <;> ring

theorem active_neuron_parameter_derivatives (w a b x : ℝ) (hactive : 0 < a * x + b) :
    HasDerivAt (fun v => neuron v a b x) (max 0 (a * x + b)) w ∧
    HasDerivAt (fun v => neuron w v b x) (w * x) a ∧
    HasDerivAt (fun v => neuron w a v x) w b ∧
    HasDerivAt (fun v => neuron w a b v) (w * a) x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [neuron, id_eq, one_mul] using (hasDerivAt_id w).mul_const (max 0 (a * x + b))
  · have hd := (active_affine_relu_derivative x b a (by nlinarith)).const_mul w
    convert hd using 1
    ext v
    simp only [neuron]
    congr 2
    ring
  · have hd := (active_affine_relu_derivative 1 (a * x) b (by nlinarith)).const_mul w
    convert hd using 1
    · ext v
      simp only [neuron, one_mul]
      congr 2
      ring
    · ring
  · exact (active_affine_relu_derivative a b x hactive).const_mul w

theorem active_neuron_loss_derivatives (w a b x y : ℝ) (hactive : 0 < a * x + b) :
    HasDerivAt (fun v => loss v a b x y)
      ((neuron w a b x - y) * max 0 (a * x + b)) w ∧
    HasDerivAt (fun v => loss w v b x y) ((neuron w a b x - y) * w * x) a ∧
    HasDerivAt (fun v => loss w a v x y) ((neuron w a b x - y) * w) b ∧
    HasDerivAt (fun v => loss w a b v y) ((neuron w a b x - y) * w * a) x := by
  have hd := active_neuron_parameter_derivatives w a b x hactive
  refine ⟨squared_loss_chain _ _ _ _ hd.1, ?_, squared_loss_chain _ _ _ _ hd.2.2.1, ?_⟩
  · exact (squared_loss_chain (fun v => neuron w v b x) (w * x) a y hd.2.1).congr_deriv (by ring)
  · exact (squared_loss_chain (fun v => neuron w a b v) (w * a) x y hd.2.2.2).congr_deriv (by ring)

theorem actual_active_neuron_values :
    (2 : ℝ) * 1 + (-1) = 1 ∧ max (0 : ℝ) (2 * 1 + (-1)) = 1 ∧
    neuron 3 2 (-1) 1 = 3 ∧ loss 3 2 (-1) 1 1 = 2 := by
  norm_num [neuron, loss]

theorem actual_output_and_hidden_loss_derivatives :
    HasDerivAt (fun f : ℝ => (f - 1) ^ 2 / 2) 2 3 ∧
    HasDerivAt (fun v : ℝ => (3 * max 0 v - 1) ^ 2 / 2) 6 1 := by
  constructor
  · convert squared_loss_chain id 1 3 1 (hasDerivAt_id 3) using 1 <;> norm_num
  · have hd := (active_affine_relu_derivative 1 0 1 (by norm_num)).const_mul 3
    have hl := squared_loss_chain (fun v : ℝ => 3 * max 0 (1 * v + 0)) 3 1 1 (by simpa using hd)
    norm_num at hl
    exact hl

theorem actual_active_neuron_loss_derivatives :
    HasDerivAt (fun w => loss w 2 (-1) 1 1) 2 3 ∧
    HasDerivAt (fun a => loss 3 a (-1) 1 1) 6 2 ∧
    HasDerivAt (fun b => loss 3 2 b 1 1) 6 (-1) ∧
    HasDerivAt (fun x => loss 3 2 (-1) x 1) 12 1 := by
  have hd := active_neuron_loss_derivatives 3 2 (-1) 1 1 (by norm_num)
  norm_num [neuron] at hd
  exact hd

end SafeLearning.CompleteAppliedBackprop
