import torus.shared.ParameterRawJetLadderGaussian
import torus.shared.ParameterRawJetLadderDifferentiation
import torus.shared.ParameterRawJetPolynomialRecurrence
import torus.shared.ParameterRawJetLadderBoundary

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Geometry TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.PlaneJetReproducing
open scoped ComplexConjugate ContDiff

def dualHermite (F : ℂ → ℂ) (j : ℕ) (R : ℂ) : ℂ :=
  conj (gaussianFactor 1 R * jetPolynomial F j R)

theorem dualHermite_differentiable (F : ℂ → ℂ) (hF : Differentiable ℂ F) (j : ℕ) :
    Differentiable ℝ (dualHermite F j) := by
  have hg : Differentiable ℝ (gaussianFactor 1) := by unfold gaussianFactor; fun_prop
  exact Complex.conjCLE.differentiable.comp (hg.mul ((jetPolynomial_contDiff F hF j).differentiable (by simp)))

theorem dualHermite_lower_succ (F : ℂ → ℂ) (hF : Differentiable ℂ F) (j : ℕ) (R : ℂ) :
    parameterLower 1 (dualHermite F (j+1)) R = ((j+1:ℕ):ℂ)*dualHermite F j R := by
  unfold dualHermite
  rw [parameterLower_conj_gaussian _ ((jetPolynomial_contDiff F hF (j+1)).differentiable (by simp)),
    jetPolynomial_wirtingerBar_sum F hF]
  rw [show j+1+1=j+2 by omega, jetPolynomial_weighted_succ_power]
  simp only [map_neg, map_mul, map_natCast]
  ring

theorem dualHermite_lower_zero (F : ℂ → ℂ) (hF : Differentiable ℂ F) (R : ℂ) :
    parameterLower 1 (dualHermite F 0) R = 0 := by
  unfold dualHermite
  rw [parameterLower_conj_gaussian _ ((jetPolynomial_contDiff F hF 0).differentiable (by simp)),
    jetPolynomial_wirtingerBar_sum F hF]
  simp

theorem dualHermite_raise (F : ℂ → ℂ) (hF : Differentiable ℂ F) (j : ℕ) (R : ℂ) :
    parameterRaise 1 (dualHermite F j) R = dualHermite F (j+1) R := by
  unfold dualHermite
  rw [parameterRaise_conj_gaussian _ ((jetPolynomial_contDiff F hF j).differentiable (by simp)),
    jetPolynomial_wirtinger F hF]
  congr 2
  rw [jetPolynomial_succ]
  ring

theorem dualRawJetScalar_finite (G : Geometry) (theta : Twist) (h : LLL G theta 1) (j : ℕ) :
    dualRawJetScalar G theta h j = fun R =>
      (Real.sqrt (j.factorial : ℝ) : ℂ)⁻¹ * dualHermite (canonicalRawStripped G theta h) j R := by
  funext R
  rw [dualRawJetScalar_eq_conj, rawJetCoefficient_finite]
  simp only [dualHermite, map_div₀, map_mul, map_inv₀, Complex.conj_ofReal, div_eq_mul_inv, mul_comm]

private theorem sqrt_factorial_succ (j : ℕ) :
    (Real.sqrt ((j+1).factorial : ℝ) : ℂ) =
      (Real.sqrt ((j+1:ℕ) : ℝ) : ℂ)*(Real.sqrt (j.factorial : ℝ) : ℂ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), Complex.ofReal_mul]

private theorem sqrt_factorial_lower_ratio (j : ℕ) :
    (Real.sqrt ((j+1).factorial : ℝ) : ℂ)⁻¹ * ((j+1:ℕ):ℂ) =
      (Real.sqrt ((j+1:ℕ):ℝ) : ℂ)*(Real.sqrt (j.factorial : ℝ) : ℂ)⁻¹ := by
  rw [sqrt_factorial_succ]
  have ha : (Real.sqrt ((j+1:ℕ):ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hb : (Real.sqrt (j.factorial:ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hs : (Real.sqrt ((j+1:ℕ):ℝ) : ℂ)^2 = ((j+1:ℕ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤(j+1:ℕ) by positivity)
  rw [← hs]
  field_simp

/-- The actual raw jet family, with its original factorial normalization. -/
theorem dualRawJetScalar_lower_succ (G : Geometry) (theta : Twist) (h : LLL G theta 1)
    (j : ℕ) :
    parameterLower 1 (dualRawJetScalar G theta h (j+1)) =
      (Real.sqrt ((j+1:ℕ):ℝ) : ℂ) • dualRawJetScalar G theta h j := by
  funext R
  rw [dualRawJetScalar_finite, parameterLower_const_mul _ _ _
    (dualHermite_differentiable _ (canonicalRawStripped_differentiable G theta h) _),
    dualHermite_lower_succ _ (canonicalRawStripped_differentiable G theta h)]
  rw [dualRawJetScalar_finite]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, sqrt_factorial_lower_ratio]
  ring

theorem dualRawJetScalar_lower_zero (G : Geometry) (theta : Twist) (h : LLL G theta 1) :
    parameterLower 1 (dualRawJetScalar G theta h 0) = 0 := by
  funext R
  rw [dualRawJetScalar_finite, parameterLower_const_mul _ _ _
    (dualHermite_differentiable _ (canonicalRawStripped_differentiable G theta h) _),
    dualHermite_lower_zero _ (canonicalRawStripped_differentiable G theta h)]
  simp

theorem dualRawJetScalar_raise (G : Geometry) (theta : Twist) (h : LLL G theta 1)
    (j : ℕ) :
    parameterRaise 1 (dualRawJetScalar G theta h j) =
      (Real.sqrt ((j+1:ℕ):ℝ) : ℂ) • dualRawJetScalar G theta h (j+1) := by
  funext R
  rw [dualRawJetScalar_finite, parameterRaise_const_mul _ _ _
    (dualHermite_differentiable _ (canonicalRawStripped_differentiable G theta h) _),
    dualHermite_raise _ (canonicalRawStripped_differentiable G theta h)]
  rw [dualRawJetScalar_finite]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [sqrt_factorial_succ]
  have ha : (Real.sqrt ((j+1:ℕ):ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp

#print axioms dualRawJetScalar_lower_succ
#print axioms dualRawJetScalar_lower_zero
#print axioms dualRawJetScalar_raise
end TorusLean.Shared.ParameterRawJetLadder
