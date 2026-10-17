import torus.shared.RelativeJetMapLeibniz
import torus.shared.ContactFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Geometry TorusLean.Shared.NormalJetBridge
open TorusLean.Shared.ChargeTwoScaling
open scoped TensorProduct ComplexConjugate BigOperators

theorem relativeBinomialCoeff_conj (d p : ℕ) :
    conj (relativeBinomialCoeff d p) = relativeBinomialCoeff d p := by
  simp only [relativeBinomialCoeff, map_mul, map_pow, map_neg, map_one, map_div₀,
    Complex.conj_ofReal, map_ofNat]

/-- Actual finite tensor of periodized physical charge-two jet kernels.
This is a derived evaluation kernel for J, not a definition of its image. -/
def relativeJetEvaluationKernel (G : Geometry) (theta : Twist) (d : ℕ) (R : ℂ) :
    LLL G theta 2 ⊗[ℂ] LLL G theta 2 :=
  ∑ p ∈ Finset.range (d+1), relativeBinomialCoeff d p •
    (chargeTwoJetKernel G theta p R ⊗ₜ[ℂ] chargeTwoJetKernel G theta (d-p) R)

/-- The finite Leibniz tensor represents the actual original local jet on
every full tensor, not merely on decomposable states. -/
theorem relativeJetEvaluationKernel_reproduces (G : Geometry) (theta : Twist)
    (d : ℕ) (R : ℂ) (ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2) :
    inner ℂ (relativeJetEvaluationKernel G theta d R) ψ =
      (relativeJet G theta 2 2 d ψ).val R := by
  induction ψ using TensorProduct.induction_on with
  | zero => simp
  | add ψ φ hψ hφ =>
    simp only [inner_add_right, map_add, hψ, hφ]
    rfl
  | tmul f g =>
    rw [relativeJet_tmul_leibniz]
    unfold relativeJetEvaluationKernel
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro p hp
    change inner ℂ ((relativeBinomialCoeff d p) • (chargeTwoJetKernel G theta p R ⊗ₜ[ℂ] chargeTwoJetKernel G theta (d-p) R) : LLL G theta 2 ⊗[ℂ] LLL G theta 2) (f ⊗ₜ[ℂ] g) = _
    rw [inner_smul_left (chargeTwoJetKernel G theta p R ⊗ₜ[ℂ] chargeTwoJetKernel G theta (d-p) R)
      (f ⊗ₜ[ℂ] g) (relativeBinomialCoeff d p), TensorProduct.inner_tmul, relativeBinomialCoeff_conj,
      chargeTwoJetKernel_reproduces, chargeTwoJetKernel_reproduces]
    ring

/-- The actual adjoint evaluated on the full charge-four evaluation kernel
is exactly the finite tensor derived from the canonical charge-two jets. -/
theorem relativeJet_adjoint_evaluationKernel (G : Geometry) (theta : Twist)
    (d : ℕ) (R : ℂ) :
    (relativeJet G theta 2 2 d).adjoint (evaluationKernel G theta 4 R) =
      relativeJetEvaluationKernel G theta d R := by
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left, evaluationKernel_reproduces,
    relativeJetEvaluationKernel_reproduces]

/-- The true J_d J_e† kernel on all COM points, reduced to a finite tensor
Gram. No periodized lattice Gram identity is assumed in this reduction. -/
theorem relativeJet_gram_evaluation (G : Geometry) (theta : Twist)
    (d e : ℕ) (R S : ℂ) :
    (relativeJet G theta 2 2 d
      ((relativeJet G theta 2 2 e).adjoint (evaluationKernel G theta 4 S))).val R =
    inner ℂ (relativeJetEvaluationKernel G theta d R)
      (relativeJetEvaluationKernel G theta e S) := by
  rw [relativeJet_adjoint_evaluationKernel, relativeJetEvaluationKernel_reproduces]

/-- Explicit finite double sum for the actual full-COM operator kernel.
Each factor is an original physical charge-two canonical jet inner product. -/
theorem relativeJet_gram_finite_sum (G : Geometry) (theta : Twist)
    (d e : ℕ) (R S : ℂ) :
    (relativeJet G theta 2 2 d
      ((relativeJet G theta 2 2 e).adjoint (evaluationKernel G theta 4 S))).val R =
    ∑ p ∈ Finset.range (d+1), ∑ q ∈ Finset.range (e+1),
      relativeBinomialCoeff d p * relativeBinomialCoeff e q *
        inner ℂ (chargeTwoJetKernel G theta p R) (chargeTwoJetKernel G theta q S) *
        inner ℂ (chargeTwoJetKernel G theta (d-p) R) (chargeTwoJetKernel G theta (e-q) S) := by
  rw [relativeJet_gram_evaluation]
  unfold relativeJetEvaluationKernel
  rw [sum_inner]
  simp_rw [inner_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  change inner ℂ ((relativeBinomialCoeff d p) • (chargeTwoJetKernel G theta p R ⊗ₜ[ℂ] chargeTwoJetKernel G theta (d-p) R) : LLL G theta 2 ⊗[ℂ] LLL G theta 2)
    ((relativeBinomialCoeff e q) • (chargeTwoJetKernel G theta q S ⊗ₜ[ℂ] chargeTwoJetKernel G theta (e-q) S) : LLL G theta 2 ⊗[ℂ] LLL G theta 2) = _
  rw [inner_smul_left (chargeTwoJetKernel G theta p R ⊗ₜ[ℂ] chargeTwoJetKernel G theta (d-p) R)
    ((relativeBinomialCoeff e q) • (chargeTwoJetKernel G theta q S ⊗ₜ[ℂ] chargeTwoJetKernel G theta (e-q) S))
    (relativeBinomialCoeff d p),
    inner_smul_right (chargeTwoJetKernel G theta p R ⊗ₜ[ℂ] chargeTwoJetKernel G theta (d-p) R)
    (chargeTwoJetKernel G theta q S ⊗ₜ[ℂ] chargeTwoJetKernel G theta (e-q) S)
    (relativeBinomialCoeff e q), relativeBinomialCoeff_conj, TensorProduct.inner_tmul]
  ring

end TorusLean.Shared.RelativeJetMap
