import torus.shared.ThermalCoherentFermionAnchoredJacobiAlgebra
import torus.shared.ThermalCoherentJacobiAnchoredWeights

/-! Exact COM sum of the true fermionic two-column coefficients. The factor
2/3 is explicitly the charge-three COM measure factor; identifying it with
the physical torus integral remains a separate theorem. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentJacobiWeights
open scoped BigOperators

def fermionAnchoredJacobiCrossWeight (d n : ℕ) : ℝ :=
  (2/3:ℝ)*fermionAnchorJacobiAmplitude n d*fermionConnectedJacobiAmplitude n d

theorem fermionAnchoredJacobiCrossWeight_eq_geometric (d n : ℕ) :
    fermionAnchoredJacobiCrossWeight d n =
      ((2/3:ℝ)*(3*(d:ℝ)-1)*(-1/3:ℝ)^d) *
        (((n+d).choose d:ℝ)*(1/3:ℝ)^n) := by
  have h2 : (2:ℝ)^d≠0 := by positivity
  unfold fermionAnchoredJacobiCrossWeight fermionAnchorJacobiAmplitude
    fermionConnectedJacobiAmplitude
  calc
    _ = (2/3:ℝ)*(3*(d:ℝ)-1)*((-1:ℝ)^d/(2:ℝ)^d)*(jacobiAmplitude n d)^2 := by
      field_simp
      <;> ring
    _ = _ := by
      rw [jacobiAmplitude_sq]
      simp only [div_pow,pow_add,one_pow]
      field_simp
      <;> ring

/-- Scalar sum from both proved source columns. This theorem does not by
itself assert a physical S3 integral, trace, or positivity statement. -/
theorem hasSum_fermionAnchoredJacobiCrossWeight (d : ℕ) :
    HasSum (fermionAnchoredJacobiCrossWeight d) ((3*(d:ℝ)-1)*(-1/2:ℝ)^d) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one d
    (by norm_num : ‖(1/3:ℝ)‖<1)).mul_left
      ((2/3:ℝ)*(3*(d:ℝ)-1)*(-1/3:ℝ)^d)
  rw [←one_div_pow] at h
  have hv : ((2/3:ℝ)*(3*(d:ℝ)-1)*(-1/3:ℝ)^d)*
      (1/(1-(1/3:ℝ)))^(d+1) = (3*(d:ℝ)-1)*(-1/2:ℝ)^d := by
    norm_num
    rw [pow_succ]
    calc
      _ = (3*(d:ℝ)-1)*((-1/3:ℝ)^d*(3/2:ℝ)^d) := by ring
      _ = _ := by rw [←mul_pow]; norm_num
  rw [hv] at h
  apply HasSum.congr_fun h
  intro n
  exact fermionAnchoredJacobiCrossWeight_eq_geometric d n

theorem hasSum_norm_fermionAnchoredJacobiCrossWeight (d : ℕ) :
    HasSum (fun n => ‖fermionAnchoredJacobiCrossWeight d n‖)
      (|3*(d:ℝ)-1| *(1/2:ℝ)^d) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one d
    (by norm_num : ‖(1/3:ℝ)‖<1)).mul_left
      ((2/3:ℝ)*|3*(d:ℝ)-1| *(1/3:ℝ)^d)
  rw [←one_div_pow] at h
  have hv : ((2/3:ℝ)*|3*(d:ℝ)-1| *(1/3:ℝ)^d)*
      (1/(1-(1/3:ℝ)))^(d+1) = |3*(d:ℝ)-1| *(1/2:ℝ)^d := by
    norm_num
    rw [pow_succ]
    calc
      _ = |3*(d:ℝ)-1| *((1/3:ℝ)^d*(3/2:ℝ)^d) := by ring
      _ = _ := by rw [←mul_pow]; norm_num
  rw [hv] at h
  apply HasSum.congr_fun h
  intro n
  rw [fermionAnchoredJacobiCrossWeight_eq_geometric,norm_mul,
    Real.norm_of_nonneg (show (0:ℝ)≤((n+d).choose d:ℝ)*(1/3:ℝ)^n by positivity)]
  simp only [norm_mul,norm_pow,Real.norm_eq_abs]
  norm_num

end TorusLean.Shared.ThermalCoherentFermionAnchored
