import torus.shared.ThermalCoherentJacobiWeights

/-! Scalar weights for the equal-charge pair-COM/spectator-COM Jacobi step.
The leading 1/2 is the original COM factor 2/4. The independent Sym²
spectator factor is part of the actual insertion map, not this scalar sum.
No partial-trace or Omega identity is asserted in this scalar file. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourWeights
open TorusLean.Shared.ThermalCoherentMoments

/-- Squared equal-charge Jacobi amplitude, including its original thermal
spectator-COM eigenvalue and the measure factor 2/4. -/
def fourCOMWeight (a : ℝ) (e n : ℕ) : ℝ :=
  (1/2:ℝ) * thermalEigenvalue a (n+e) * ((n+e).choose e:ℝ) * (1/2:ℝ)^(n+e)

theorem fourCOMWeight_nonneg (a : ℝ) (ha : 0<a) (e n : ℕ) :
    0 ≤ fourCOMWeight a e n := by
  have h := (thermalEigenvalue_pos a ha (n+e)).le
  unfold fourCOMWeight
  positivity

theorem fourCOMWeight_geometric (a : ℝ) (e n : ℕ) :
    fourCOMWeight a e n = (1/(2*(1+a)))^(e+1) *
      (((n+e).choose e:ℝ) * (1/(2*(1+a)))^n) := by
  simp only [fourCOMWeight, thermalEigenvalue, div_eq_mul_inv, mul_pow,
    pow_add, pow_succ, mul_inv, inv_pow, one_pow]
  ring

/-- The COM trace sum is genuinely convergent and has exactly r2^(e+1),
where r2=1/(1+2a). -/
theorem hasSum_fourCOMWeight (a : ℝ) (ha : 0<a) (e : ℕ) :
    HasSum (fourCOMWeight a e) ((1/(1+2*a))^(e+1)) := by
  have hden : 0 < 2*(1+a) := by positivity
  have hratio : (1:ℝ)/(2*(1+a)) < 1 := (div_lt_one hden).2 (by linarith)
  have hnorm : ‖(1:ℝ)/(2*(1+a))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hden)]
    exact hratio
  have hquot : ((1:ℝ)/(2*(1+a))) / (1-(1:ℝ)/(2*(1+a))) = 1/(1+2*a) := by
    rw [one_sub_div hden.ne', div_div_div_cancel_right₀ hden.ne',
      show 2*(1+a)-1=1+2*a by ring]
  have hvalue : ((1:ℝ)/(2*(1+a)))^(e+1) *
      (1/(1-(1:ℝ)/(2*(1+a)))^(e+1)) = (1/(1+2*a))^(e+1) := by
    rw [mul_one_div, ← div_pow, hquot]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one e hnorm).mul_left
    (((1:ℝ)/(2*(1+a)))^(e+1))
  rw [hvalue] at h
  convert h using 1
  funext n
  exact fourCOMWeight_geometric a e n

theorem tsum_fourCOMWeight (a : ℝ) (ha : 0<a) (e : ℕ) :
    ∑' n, fourCOMWeight a e n = (1/(1+2*a))^(e+1) :=
  (hasSum_fourCOMWeight a ha e).tsum_eq

/-- The untouched spectator-difference mode contributes the independent
r1^(d+1), with r1=1/(1+a). All degrees are covered; odd d is removed by
actual symmetric insertion, not by modifying this scalar identity. -/
theorem hasSum_fourRelativeWeight (a : ℝ) (ha : 0<a) (d e : ℕ) :
    HasSum (fun n => thermalEigenvalue a d * fourCOMWeight a e n)
      ((1/(1+a))^(d+1) * (1/(1+2*a))^(e+1)) := by
  simpa only [thermalEigenvalue, one_div, inv_pow] using
    (hasSum_fourCOMWeight a ha e).mul_left (thermalEigenvalue a d)

end TorusLean.Shared.ThermalCoherentJacobiFourWeights
