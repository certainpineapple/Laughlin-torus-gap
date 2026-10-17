import torus.shared.BosonPlaneKernelProduct
import torus.shared.BosonHalfLatticeSum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.BosonContactKernelSum
open TorusLean.Geometry TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.BosonPlaneKernelProduct

def differenceEquiv : ((ℤ × ℤ) × (ℤ × ℤ)) ≃ ((ℤ × ℤ) × (ℤ × ℤ)) where
  toFun t := (t.2+t.1,t.2)
  invFun t := (t.1-t.2,t.2)
  left_inv t := by ext <;> simp
  right_inv t := by ext <;> simp

theorem evaluationKernel_one_periodization (G : Geometry) (theta : Twist) (S z : ℂ) :
    (evaluationKernel G theta 1 S).val z =
      magneticPeriodization G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
        (magneticTranslate 1 S (gaussianFactor 1)) z := by
  rw [TorusLean.Shared.BosonContactKernel.evaluationKernel_one_eq_rawPlaneJet]
  change rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 0 S z = _
  simp only [rawJetFunction, translatedPlaneJet, planeJet_zero]

theorem evaluationKernel_square_sum (G : Geometry) (theta : Twist) (S z : ℂ) :
    ((evaluationKernel G theta 1 S).val z)^2 =
      ∑' q : ℤ × ℤ, (Real.exp (-‖latticePeriod G.omega1 G.omega2 q‖^2/4) : ℂ) *
        (latticeChi G.M theta.theta1 theta.theta2 q)⁻¹ *
        magneticTranslate 2 (latticePeriod G.omega1 G.omega2 q/2)
          (evaluationKernel G theta 2 S).val z := by
  let f : (ℤ × ℤ) → ℂ := fun p => magneticImage G.M 1 G.omega1 G.omega2
    theta.theta1 theta.theta2 (magneticTranslate 1 S (gaussianFactor 1)) p z
  have hf : Summable (fun p => ‖f p‖) := by
    simpa only [f, translatedPlaneJet, planeJet_zero] using
      translatedPlaneJet_hasAbsolutelySummableImages G theta 0 S z
  have hp := summable_mul_of_summable_norm hf hf
  have he : Summable (fun t : (ℤ × ℤ) × (ℤ × ℤ) => f (t.2+t.1)*f t.2) := by
    exact hp.comp_injective (i := differenceEquiv) differenceEquiv.injective
  rw [evaluationKernel_one_periodization, pow_two]
  change (∑' p, f p) * (∑' p, f p) = _
  rw [tsum_mul_tsum_of_summable_norm hf hf, ← differenceEquiv.tsum_eq]
  change (∑' t : (ℤ × ℤ) × (ℤ × ℤ), f (t.2+t.1)*f t.2) = _
  rw [he.tsum_prod]
  apply tsum_congr
  intro q
  simp_rw [f, magneticImage_product_reindex]
  rw [tsum_mul_left]
  congr 1
  unfold magneticTranslate
  rw [tsum_mul_left]
  congr 1
  rw [evaluationKernel_two_periodization]
  rfl

open TorusLean.Shared.BosonHalfLatticeSum
open TorusLean.Shared.FractionalTranslationIsometry
open TorusLean.Fermion.LatticePacking

theorem halfLatticeOperator_apply (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (f : LLL G theta 2) (z : ℂ) :
    (halfLatticeOperator G theta f).val z =
      ∑' q : ℤ × ℤ, (Real.exp (-‖latticePeriod G.omega1 G.omega2 q‖^2/4) : ℂ) *
        (latticeChi G.M theta.theta1 theta.theta2 q)⁻¹ *
        magneticTranslate 2 (latticePeriod G.omega1 G.omega2 q/2) f.val z := by
  have ht := ((lllEvaluation G theta 2 z).comp
    (ContinuousLinearMap.apply ℂ (LLL G theta 2) f)).map_tsum
      (halfLatticeTerm_summable G theta hG)
  change (halfLatticeOperator G theta f).val z = _ at ht
  rw [ht]
  apply tsum_congr
  intro q
  change ((halfLatticeTerm G theta q) f).val z = _
  simp only [halfLatticeTerm, ContinuousLinearMap.smul_apply]
  change ((Real.exp (-‖TorusLean.Fermion.LatticePacking.period G q‖^2/4) : ℂ) *
    (latticeChi G.M theta.theta1 theta.theta2 q)⁻¹) *
    (fractionalTranslationIsometry G theta 2 1 q f).val z = _
  rw [fractionalTranslationIsometry_apply]
  congr 2
  unfold fractionalDisplacement
  push_cast
  ring

theorem continuousLinearMap_eq_of_kernels (G : Geometry) (theta : Twist)
    (A B : LLL G theta 2 →L[ℂ] LLL G theta 2)
    (h : ∀ S : ℂ, A (evaluationKernel G theta 2 S) = B (evaluationKernel G theta 2 S)) :
    A = B := by
  have ha : A.adjoint = B.adjoint := by
    ext f
    apply Subtype.ext
    funext z
    rw [← evaluationKernel_reproduces G theta 2 z,
      ← evaluationKernel_reproduces G theta 2 z,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right, h]
  have hh := congrArg (fun T : LLL G theta 2 →L[ℂ] LLL G theta 2 => T.adjoint) ha
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hh

theorem contactQQadjoint_eq_halfLatticeOperator (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) :
    (contactQ G theta).comp (contactQ G theta).adjoint = halfLatticeOperator G theta := by
  apply continuousLinearMap_eq_of_kernels G theta
  intro S
  apply Subtype.ext
  funext z
  change (contactQ G theta ((contactQ G theta).adjoint (evaluationKernel G theta 2 S))).val z = _
  rw [TorusLean.Shared.BosonContactKernel.contactQQadjoint_kernel,
    ← TorusLean.Shared.BosonContactKernel.evaluationKernel_one_eq_rawPlaneJet,
    ← TorusLean.Shared.BosonContactKernel.evaluationKernel_one_eq_rawPlaneJet,
    evaluationKernel_reproduces, evaluationKernel_square_sum,
    halfLatticeOperator_apply G theta hG]

theorem contactQQadjoint_defect_bound (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖(contactQ G theta).comp (contactQ G theta).adjoint -
      ContinuousLinearMap.id ℂ (LLL G theta 2)‖ ≤
        Real.exp (-L^2/8) * gaussianConstant := by
  rw [contactQQadjoint_eq_halfLatticeOperator G theta (hL1.trans hL)]
  exact halfLatticeOperator_defect_bound G theta L hL1 hL

#print axioms evaluationKernel_one_periodization
#print axioms evaluationKernel_square_sum
#print axioms halfLatticeOperator_apply
#print axioms continuousLinearMap_eq_of_kernels
#print axioms contactQQadjoint_eq_halfLatticeOperator
#print axioms contactQQadjoint_defect_bound
end TorusLean.Shared.BosonContactKernelSum
