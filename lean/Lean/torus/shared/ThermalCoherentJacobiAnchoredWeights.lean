import torus.shared.ThermalCoherentJacobiWeights

/-! Exact cross coefficients for the second, pair-COM column in the anchored
three-body kernel. The sign is a relative-degree sign, while the COM series
is absolutely summable. The scalar 2/3 here is explicitly the separate COM
measure factor; this file alone does not prove the physical cell identity. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiAnchored
open TorusLean.Shared.ThermalCoherentJacobiWeights

/-- The signed normalized pair-COM column. Equivalently its unsigned part
is sqrt(choose(n+d,d) * (2/3)^n * (1/3)^d). -/
def pairAnchoredJacobiAmplitude (n d : ℕ) : ℝ :=
  (-1:ℝ)^d * (2:ℝ)^n * jacobiAmplitude n d / (Real.sqrt (2:ℝ))^(n+d)

/-- Original scalar multiplying the off-diagonal two-column source rank. -/
def anchoredKernelCoefficient (l : ℕ) : ℝ := 2 / (Real.sqrt (2:ℝ))^l

theorem anchoredJacobi_cross_coefficient (n d : ℕ) :
    anchoredKernelCoefficient (n+d) * jacobiAmplitude n d * pairAnchoredJacobiAmplitude n d =
      2*(-1:ℝ)^d*((n+d).choose d:ℝ)/(3:ℝ)^(n+d) := by
  have hs : (Real.sqrt (2:ℝ))^(n+d)≠0 := pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have hsq : (Real.sqrt (2:ℝ))^(n+d)*(Real.sqrt (2:ℝ))^(n+d)=(2:ℝ)^(n+d) := by
    rw [←mul_pow,Real.mul_self_sqrt (by norm_num)]
  unfold anchoredKernelCoefficient pairAnchoredJacobiAmplitude
  calc
    _ = (2*(-1:ℝ)^d*(2:ℝ)^n*(jacobiAmplitude n d)^2) /
        ((Real.sqrt (2:ℝ))^(n+d)*(Real.sqrt (2:ℝ))^(n+d)) := by field_simp [hs]
    _ = _ := by
      rw [hsq,jacobiAmplitude_sq]
      simp only [div_pow,one_pow,pow_add]
      field_simp

/-- Cross coefficient including exactly one charge-three COM measure factor. -/
def anchoredJacobiCrossWeight (d n : ℕ) : ℝ :=
  (2/3:ℝ)*anchoredKernelCoefficient (n+d)*jacobiAmplitude n d*pairAnchoredJacobiAmplitude n d

theorem anchoredJacobiCrossWeight_eq_geometric (d n : ℕ) :
    anchoredJacobiCrossWeight d n =
      ((4/3:ℝ)*(-1/3:ℝ)^d) * (((n+d).choose d:ℝ)*(1/3:ℝ)^n) := by
  have h := anchoredJacobi_cross_coefficient n d
  unfold anchoredJacobiCrossWeight
  rw [show (2/3:ℝ)*anchoredKernelCoefficient (n+d)*jacobiAmplitude n d*pairAnchoredJacobiAmplitude n d =
    (2/3:ℝ)*(anchoredKernelCoefficient (n+d)*jacobiAmplitude n d*pairAnchoredJacobiAmplitude n d) by ring,h]
  simp only [div_pow,pow_add,one_pow]
  field_simp <;> ring

private theorem anchored_binomial_value (d : ℕ) (s : ℝ) :
    ((4/3:ℝ)*(s/3)^d)*(1/(1-(1/3:ℝ)))^(d+1) = 2*(s/2)^d := by
  norm_num
  rw [pow_succ]
  calc
    _ = 2*((s/3)^d*(3/2:ℝ)^d) := by ring
    _ = _ := by rw [←mul_pow]; congr 1; ring

theorem hasSum_anchoredJacobiCrossWeight (d : ℕ) :
    HasSum (anchoredJacobiCrossWeight d) (2*(-1/2:ℝ)^d) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one d
    (by norm_num : ‖(1/3:ℝ)‖<1)).mul_left ((4/3:ℝ)*(-1/3:ℝ)^d)
  rw [←one_div_pow,anchored_binomial_value d (-1)] at h
  apply HasSum.congr_fun h
  intro n
  exact anchoredJacobiCrossWeight_eq_geometric d n

/-- Absolute summability is genuine, not inferred from cancellation. -/
theorem hasSum_norm_anchoredJacobiCrossWeight (d : ℕ) :
    HasSum (fun n => ‖anchoredJacobiCrossWeight d n‖) (2*(1/2:ℝ)^d) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one d
    (by norm_num : ‖(1/3:ℝ)‖<1)).mul_left ((4/3:ℝ)*(1/3:ℝ)^d)
  rw [←one_div_pow,anchored_binomial_value d 1] at h
  apply HasSum.congr_fun h
  intro n
  rw [anchoredJacobiCrossWeight_eq_geometric,norm_mul,
    Real.norm_of_nonneg (show (0:ℝ)≤((n+d).choose d:ℝ)*(1/3:ℝ)^n by positivity)]
  simp only [norm_mul,norm_pow,Real.norm_eq_abs]
  norm_num

end TorusLean.Shared.ThermalCoherentJacobiAnchored
