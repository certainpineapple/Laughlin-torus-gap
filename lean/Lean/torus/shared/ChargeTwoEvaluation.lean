import torus.shared.ChargeTwoIsometry

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.ChargeTwoEvaluation

open TorusLean.Shared.ChargeTwoScaling TorusLean.Shared.ChargeTwoIsometry
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PlaneJetGramBounds
open TorusLean.Fermion.LatticePacking TorusLean.Fermion.LatticeLaguerreSum

theorem canonicalJetEvaluation_zero (G : Geometry) (theta : Twist) (R : ℂ) :
    canonicalJetEvaluation G theta 0 R = lllEvaluation G theta 1 R := by
  ext f
  exact rawJetCoefficient_zero G theta f R

theorem evaluation_one_norm (G : Geometry) (theta : Twist) (R : ℂ) :
    ‖lllEvaluation G theta 1 R‖ = ‖rawPlaneJet G theta 0 R‖ := by
  rw [rawPlaneJet_eq_canonicalJetEvaluationKernel, canonicalJetEvaluationKernel_norm,
    canonicalJetEvaluation_zero]

/-- Actual evaluation intertwines the full charge-two/charge-one isometry. -/
theorem evaluation_scaling (G : Geometry) (theta : Twist) (R : ℂ)
    (f : LLL (scaledGeometry G) (scaledTwist theta) 1) :
    lllEvaluation G theta 2 R (scalingLinearIsometryEquiv G theta f) =
      lllEvaluation (scaledGeometry G) (scaledTwist theta) 1 ((scale : ℂ)*R) f := rfl

theorem evaluation_two_norm (G : Geometry) (theta : Twist) (R : ℂ) :
    ‖lllEvaluation G theta 2 R‖ =
      ‖lllEvaluation (scaledGeometry G) (scaledTwist theta) 1 ((scale : ℂ)*R)‖ := by
  let e := scalingLinearIsometryEquiv G theta
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    obtain ⟨g, rfl⟩ := e.surjective f
    rw [show lllEvaluation G theta 2 R (e g) =
      lllEvaluation (scaledGeometry G) (scaledTwist theta) 1 ((scale : ℂ)*R) g from rfl,
      e.norm_map]
    exact (lllEvaluation _ _ _ _).le_opNorm g
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro g
    rw [← evaluation_scaling]
    exact ((lllEvaluation G theta 2 R).le_opNorm (e g)).trans_eq
      (by rw [e.norm_map])

theorem scale_ge_one : 1 ≤ scale := by
  have := scale_sq
  have := scale_pos
  nlinarith

/-- Charge-two evaluation error on the actual cell-Hilbert carrier. -/
theorem evaluation_two_norm_sq_sub_one_le (G : Geometry) (theta : Twist)
    (R : ℂ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    |‖lllEvaluation G theta 2 R‖^2 - 1| ≤
      Real.exp (-L^2 / 4) * gaussianConstant := by
  rw [evaluation_two_norm, evaluation_one_norm]
  have h := rawPlaneJet_norm_sq_sub_one_le (scaledGeometry G) (scaledTwist theta)
    0 ((scale : ℂ)*R) (scale*L)
    (by nlinarith [scale_ge_one]) (scaled_systole_lower G L hL)
    (by simp only [Nat.cast_zero, mul_zero]; positivity)
  have he : -(scale*L)^2 / 8 = -L^2/4 := by rw [mul_pow, scale_sq]; ring
  simpa only [he] using h

#print axioms canonicalJetEvaluation_zero
#print axioms evaluation_one_norm
#print axioms evaluation_scaling
#print axioms evaluation_two_norm
#print axioms scale_ge_one
#print axioms evaluation_two_norm_sq_sub_one_le

end TorusLean.Shared.ChargeTwoEvaluation
