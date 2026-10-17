import torus.shared.ContactFrame
import torus.shared.ChargeTwoEvaluation
import torus.shared.PlaneJetLaguerreGram

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonContactKernel
open TorusLean.Boson.Sym2Evaluation
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.ChargeTwoEvaluation

theorem evaluationKernel_one_eq_rawPlaneJet (G : Geometry) (theta : Twist) (R : ℂ) :
    evaluationKernel G theta 1 R = rawPlaneJet G theta 0 R := by
  rw [rawPlaneJet_eq_canonicalJetEvaluationKernel, canonicalJetEvaluationKernel,
    canonicalJetEvaluation_zero]
  rfl

theorem contactQ_adjoint_evaluationKernel (G : Geometry) (theta : Twist) (R : ℂ) :
    (contactQ G theta).adjoint (evaluationKernel G theta 2 R) = rawBosonPair G theta R := by
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left, evaluationKernel_reproduces, contactQ_evaluation]

theorem rawBosonPair_inner (G : Geometry) (theta : Twist) (R S : ℂ) :
    inner ℂ (rawBosonPair G theta R) (rawBosonPair G theta S) =
      (inner ℂ (evaluationKernel G theta 1 R) (evaluationKernel G theta 1 S))^2 := by
  change inner ℂ (symTensor _ _) (symTensor _ _) = _
  rw [symTensor_inner]
  ring

/-- Exact kernel of Q Q-adjoint on the complete physical charge-two space.
This supplies the actual operator whose Schur error must be bounded; a density
bound alone is not asserted to imply the required operator estimate. -/
theorem contactQQadjoint_kernel (G : Geometry) (theta : Twist) (R S : ℂ) :
    (contactQ G theta ((contactQ G theta).adjoint (evaluationKernel G theta 2 S))).val R =
      (inner ℂ (rawPlaneJet G theta 0 R) (rawPlaneJet G theta 0 S))^2 := by
  rw [contactQ_evaluation, contactQ_adjoint_evaluationKernel, rawBosonPair_inner,
    evaluationKernel_one_eq_rawPlaneJet, evaluationKernel_one_eq_rawPlaneJet]

open TorusLean.Shared.ChargeTwoScaling TorusLean.Shared.ChargeTwoIsometry

theorem evaluationKernel_two_scaled (G : Geometry) (theta : Twist) (R : ℂ) :
    scalingLinearIsometryEquiv G theta
      (evaluationKernel (scaledGeometry G) (scaledTwist theta) 1 ((scale : ℂ)*R)) =
      evaluationKernel G theta 2 R := by
  apply ext_inner_right ℂ
  intro f
  obtain ⟨g, rfl⟩ := (scalingLinearIsometryEquiv G theta).surjective f
  rw [(scalingLinearIsometryEquiv G theta).inner_map_map,
    evaluationKernel_reproduces, evaluationKernel_reproduces]
  rfl

theorem evaluationKernel_two_inner (G : Geometry) (theta : Twist) (R S : ℂ) :
    inner ℂ (evaluationKernel G theta 2 R) (evaluationKernel G theta 2 S) =
      inner ℂ (rawPlaneJet (scaledGeometry G) (scaledTwist theta) 0 ((scale : ℂ)*R))
        (rawPlaneJet (scaledGeometry G) (scaledTwist theta) 0 ((scale : ℂ)*S)) := by
  rw [← evaluationKernel_two_scaled, ← evaluationKernel_two_scaled,
    (scalingLinearIsometryEquiv G theta).inner_map_map,
    evaluationKernel_one_eq_rawPlaneJet, evaluationKernel_one_eq_rawPlaneJet]

/-- The genuine frame defect kernel, with the charge-two identity kernel
subtracted before any attempted error estimate. -/
theorem contactQQadjoint_defect_kernel (G : Geometry) (theta : Twist) (R S : ℂ) :
    (((contactQ G theta).comp (contactQ G theta).adjoint -
      ContinuousLinearMap.id ℂ (LLL G theta 2)) (evaluationKernel G theta 2 S)).val R =
      (inner ℂ (rawPlaneJet G theta 0 R) (rawPlaneJet G theta 0 S))^2 -
        inner ℂ (rawPlaneJet (scaledGeometry G) (scaledTwist theta) 0 ((scale : ℂ)*R))
          (rawPlaneJet (scaledGeometry G) (scaledTwist theta) 0 ((scale : ℂ)*S)) := by
  change (contactQ G theta ((contactQ G theta).adjoint (evaluationKernel G theta 2 S))).val R -
    (evaluationKernel G theta 2 S).val R = _
  rw [contactQQadjoint_kernel, ← evaluationKernel_reproduces G theta 2 R,
    evaluationKernel_two_inner]

#print axioms evaluationKernel_one_eq_rawPlaneJet
#print axioms contactQ_adjoint_evaluationKernel
#print axioms rawBosonPair_inner
#print axioms contactQQadjoint_kernel
#print axioms evaluationKernel_two_scaled
#print axioms evaluationKernel_two_inner
#print axioms contactQQadjoint_defect_kernel
end TorusLean.Shared.BosonContactKernel
