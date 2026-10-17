import torus.shared.FermionRelativeFrameSections
import torus.shared.RelativeJetMapOscillator

/-! The actual charge-one m=1 relative derivative on the complete tensor.
Its normalized antisymmetric pure tensor is the original unrescaled raw B0;
its adjoint range is genuinely antisymmetric in the inherited tensor norm. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionM1NearProjection
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.NormalJetBridge TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionJetPair
open TorusLean.Shared.PhysicalFermionPairLift TorusLean.Shared.PhysicalFermionPairAnchor
open TorusLean.Shared.PhysicalFermionExterior TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.ChargeTwoScaling
open scoped TensorProduct ComplexConjugate BigOperators

/-- The already constructed full-domain, full-charge-two actual local jet. -/
def m1Q (G : Geometry) (theta : Twist) :
    (LLL G theta 1 ⊗[ℂ] LLL G theta 1) →L[ℂ] LLL G theta 2 :=
  relativeJet G theta 1 1 1

lemma jetScale_m1_inv : (jetScale 1 1 1)⁻¹ = (scale : ℂ) := by
  have h := pairAnchorScale_jetScale 0
  norm_num [pairAnchorScale, sqrtFactorial, scale] at h ⊢
  exact h

lemma canonical_product_derivative (G : Geometry) (theta : Twist)
    (f g : LLL G theta 1) (R : ℂ) :
    deriv (fun r : ℂ => canonicalRawStripped G theta f (R+r/2) *
      canonicalRawStripped G theta g (R-r/2)) 0 =
      (deriv (canonicalRawStripped G theta f) R * canonicalRawStripped G theta g R -
        canonicalRawStripped G theta f R * deriv (canonicalRawStripped G theta g) R) / 2 := by
  have hp : HasDerivAt (fun r : ℂ => R+r/2) (1/2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).div_const 2).const_add R
  have hm : HasDerivAt (fun r : ℂ => R-r/2) (-(1/2)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).div_const 2).const_sub R
  have hf : HasDerivAt (canonicalRawStripped G theta f)
      (deriv (canonicalRawStripped G theta f) R) (R+0/2) := by
    simpa using (canonicalRawStripped_differentiable G theta f R).hasDerivAt
  have hg : HasDerivAt (canonicalRawStripped G theta g)
      (deriv (canonicalRawStripped G theta g) R) (R-0/2) := by
    simpa using (canonicalRawStripped_differentiable G theta g R).hasDerivAt
  have h := ((hf.comp 0 hp).fun_mul (hg.comp 0 hm)).deriv
  simp only [Function.comp_apply, zero_div, add_zero, sub_zero] at h
  rw [h]
  ring

/-- Actual J1 on arbitrary physical orbitals, including its original 1/sqrt2. -/
theorem m1Q_tmul (G : Geometry) (theta : Twist) (f g : LLL G theta 1) (R : ℂ) :
    (m1Q G theta (f ⊗ₜ[ℂ] g)).val R = (scale : ℂ)/2 *
      (rawJetCoefficient G theta f 1 R * rawJetCoefficient G theta g 0 R -
        rawJetCoefficient G theta f 0 R * rawJetCoefficient G theta g 1 R) := by
  have hfactor (z : ℂ × ℂ) : rawPairFunction G theta 1 1 (f ⊗ₜ[ℂ] g) z =
      1 * (gaussianFactor 1 z.1 * gaussianFactor 1 z.2) *
        (canonicalRawStripped G theta f z.1 * canonicalRawStripped G theta g z.2) := by
    rw [rawPairFunction_tmul_apply, canonicalRawStripped_factor G theta f,
      canonicalRawStripped_factor G theta g]
    ring
  have h := localNormalJet_gaussian_factor 1 1 (by norm_num) 1 _ _ 1 hfactor R
  change (relativeJet G theta 1 1 1 (f ⊗ₜ[ℂ] g)).val R = _
  rw [relativeJet_apply]
  simp only [Nat.cast_one]
  rw [h]
  simp only [one_mul, iteratedDeriv_one, jetScale_m1_inv,
    show (1 : ℝ)+1=2 by norm_num]
  have hc : (fun r : ℂ => canonicalRawStripped G theta f (jacobiFirst 1 1 R r) *
      canonicalRawStripped G theta g (jacobiSecond 1 1 R r)) =
      (fun r => canonicalRawStripped G theta f (R+r/2) *
        canonicalRawStripped G theta g (R-r/2)) := by
    funext r
    have h₁ : jacobiFirst 1 1 R r = R+r/2 := by norm_num [jacobiFirst] <;> ring
    have h₂ : jacobiSecond 1 1 R r = R-r/2 := by norm_num [jacobiSecond] <;> ring
    rw [h₁,h₂]
  rw [hc, canonical_product_derivative, rawJetCoefficient_one_formula,
    rawJetCoefficient_one_formula, rawJetCoefficient_zero, rawJetCoefficient_zero,
    canonicalRawStripped_factor G theta f, canonicalRawStripped_factor G theta g,
    ← gaussian_one_mul_self]
  ring

/-- The original normalized two-slot antisymmetric tensor, in the actual
full tensor carrier and its inherited physical Hilbert norm. -/
def normalizedSlaterTensor (G : Geometry) (theta : Twist) (f g : LLL G theta 1) :
    LLL G theta 1 ⊗[ℂ] LLL G theta 1 :=
  ((scale : ℂ)/2) • (f ⊗ₜ[ℂ] g - g ⊗ₜ[ℂ] f)

/-- The sqrt2 from antisymmetry cancels J1's 1/sqrt2 exactly, giving the
unchanged paper -u0 wedge u1 CAR determinant on every pair of actual orbitals. -/
theorem m1Q_normalizedSlater_original_pair (G : Geometry) (theta : Twist)
    (f g : LLL G theta 1) (R : ℂ) :
    (m1Q G theta (normalizedSlaterTensor G theta f g)).val R =
      rawPairGram (physicalQ G theta)
        (-physicalJetCoordinates G theta 0 R) (physicalJetCoordinates G theta 1 R)
        (physicalOrbitalCoordinates G theta f) (physicalOrbitalCoordinates G theta g) := by
  have hn (Q : ℕ) (v w : Orbital Q) : rawGram Q (-v) w = -rawGram Q v w := by
    simp [rawGram_eq_sum, neg_mul, Finset.sum_neg_distrib]
  change lllEvaluation G theta 2 R (m1Q G theta (normalizedSlaterTensor G theta f g)) = _
  simp only [normalizedSlaterTensor, map_smul, map_sub, smul_eq_mul, lllEvaluation_apply]
  rw [m1Q_tmul, m1Q_tmul]
  simp only [rawPairGram, hn, physicalJetCoordinates_reproduces]
  linear_combination (rawJetCoefficient G theta f 1 R * rawJetCoefficient G theta g 0 R -
    rawJetCoefficient G theta f 0 R * rawJetCoefficient G theta g 1 R)/2 * scale_complex_sq

/-- Odd relative degree is odd under actual tensor exchange. -/
theorem m1Q_exchange (G : Geometry) (theta : Twist)
    (ψ : LLL G theta 1 ⊗[ℂ] LLL G theta 1) :
    m1Q G theta (TensorProduct.comm ℂ _ _ ψ) = -m1Q G theta ψ := by
  induction ψ using TensorProduct.induction_on with
  | zero => simp
  | add ψ φ hψ hφ => simp only [map_add, hψ, hφ, neg_add]
  | tmul f g =>
      apply Subtype.ext
      funext R
      change (m1Q G theta (g ⊗ₜ[ℂ] f)).val R = -(m1Q G theta (f ⊗ₜ[ℂ] g)).val R
      rw [m1Q_tmul, m1Q_tmul]
      ring

/-- No exterior-space Hilbert structure is assumed: the actual full-tensor
adjoint has antisymmetric range by the proved exchange identity. -/
theorem m1Q_adjoint_antisymmetric (G : Geometry) (theta : Twist) (f : LLL G theta 2) :
    TensorProduct.comm ℂ (LLL G theta 1) (LLL G theta 1) ((m1Q G theta).adjoint f) =
      -(m1Q G theta).adjoint f := by
  apply ext_inner_right ℂ
  intro ψ
  have h := TensorProduct.inner_comm_comm (𝕜 := ℂ)
    ((m1Q G theta).adjoint f) (TensorProduct.comm ℂ _ _ ψ)
  simp only [TensorProduct.comm_comm] at h
  rw [h, ContinuousLinearMap.adjoint_inner_left, m1Q_exchange,
    inner_neg_right, inner_neg_left, ContinuousLinearMap.adjoint_inner_left]

/-- The Riesz kernel is a finite tensor of the original charge-one raw jets. -/
def m1EvaluationKernel (G : Geometry) (theta : Twist) (R : ℂ) :
    LLL G theta 1 ⊗[ℂ] LLL G theta 1 :=
  ∑ p ∈ Finset.range 2, relativeBinomialCoeff 1 p •
    (rawPlaneJet G theta p R ⊗ₜ[ℂ] rawPlaneJet G theta (1-p) R)

theorem m1EvaluationKernel_reproduces (G : Geometry) (theta : Twist) (R : ℂ)
    (ψ : LLL G theta 1 ⊗[ℂ] LLL G theta 1) :
    inner ℂ (m1EvaluationKernel G theta R) ψ = (m1Q G theta ψ).val R := by
  induction ψ using TensorProduct.induction_on with
  | zero => simp
  | add ψ φ hψ hφ => simp only [inner_add_right, map_add, hψ, hφ]; rfl
  | tmul f g =>
      rw [m1Q_tmul]
      unfold m1EvaluationKernel
      rw [sum_inner]
      have ht (p : ℕ) :
          inner ℂ ((relativeBinomialCoeff 1 p) •
            (rawPlaneJet G theta p R ⊗ₜ[ℂ] rawPlaneJet G theta (1-p) R) :
              LLL G theta 1 ⊗[ℂ] LLL G theta 1) (f ⊗ₜ[ℂ] g) =
          relativeBinomialCoeff 1 p * rawJetCoefficient G theta f p R *
            rawJetCoefficient G theta g (1-p) R := by
        rw [inner_smul_left (rawPlaneJet G theta p R ⊗ₜ[ℂ] rawPlaneJet G theta (1-p) R)
          (f ⊗ₜ[ℂ] g) (relativeBinomialCoeff 1 p), relativeBinomialCoeff_conj,
          TensorProduct.inner_tmul, rawPlaneJet_inner_reproduces, rawPlaneJet_inner_reproduces]
        ring
      simp_rw [ht]
      norm_num [Finset.sum_range_succ, relativeBinomialCoeff]
      ring

theorem m1Q_adjoint_evaluationKernel (G : Geometry) (theta : Twist) (R : ℂ) :
    (m1Q G theta).adjoint (evaluationKernel G theta 2 R) = m1EvaluationKernel G theta R := by
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left, evaluationKernel_reproduces,
    m1EvaluationKernel_reproduces]

/-- True QQ-adjoint on full charge-two evaluation kernels is a finite Gram
of original charge-one raw jets, with no charge/flux rescaling. -/
theorem m1Q_gram_finite_sum (G : Geometry) (theta : Twist) (R S : ℂ) :
    (m1Q G theta ((m1Q G theta).adjoint (evaluationKernel G theta 2 S))).val R =
      ∑ p ∈ Finset.range 2, ∑ q ∈ Finset.range 2,
        relativeBinomialCoeff 1 p * relativeBinomialCoeff 1 q *
          inner ℂ (rawPlaneJet G theta p R) (rawPlaneJet G theta q S) *
          inner ℂ (rawPlaneJet G theta (1-p) R) (rawPlaneJet G theta (1-q) S) := by
  rw [m1Q_adjoint_evaluationKernel, ← m1EvaluationKernel_reproduces]
  unfold m1EvaluationKernel
  rw [sum_inner]
  simp_rw [inner_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  change inner ℂ ((relativeBinomialCoeff 1 p) •
      (rawPlaneJet G theta p R ⊗ₜ[ℂ] rawPlaneJet G theta (1-p) R) :
        LLL G theta 1 ⊗[ℂ] LLL G theta 1)
    ((relativeBinomialCoeff 1 q) •
      (rawPlaneJet G theta q S ⊗ₜ[ℂ] rawPlaneJet G theta (1-q) S) :
        LLL G theta 1 ⊗[ℂ] LLL G theta 1) = _
  rw [inner_smul_left (rawPlaneJet G theta p R ⊗ₜ[ℂ] rawPlaneJet G theta (1-p) R)
    ((relativeBinomialCoeff 1 q) • (rawPlaneJet G theta q S ⊗ₜ[ℂ] rawPlaneJet G theta (1-q) S))
    (relativeBinomialCoeff 1 p),
    inner_smul_right (rawPlaneJet G theta p R ⊗ₜ[ℂ] rawPlaneJet G theta (1-p) R)
    (rawPlaneJet G theta q S ⊗ₜ[ℂ] rawPlaneJet G theta (1-q) S)
    (relativeBinomialCoeff 1 q), relativeBinomialCoeff_conj, TensorProduct.inner_tmul]
  ring

/-- The actual QQ-adjoint evaluation kernel is the original raw two-vector
CAR determinant.  This identity keeps the unrescaled physical B0 kernel. -/
theorem m1Q_gram_eq_pairGramAt (G : Geometry) (theta : Twist) (R S : ℂ) :
    (m1Q G theta ((m1Q G theta).adjoint (evaluationKernel G theta 2 S))).val R =
      PhysicalFermionNormalSquare.pairGramAt G theta R S := by
  have hg (a b : LLL G theta 1) :
      rawGram (physicalQ G theta) (physicalOrbitalCoordinates G theta a)
        (physicalOrbitalCoordinates G theta b) = inner ℂ a b :=
    (physicalOrbitalCoordinates_gram G theta a b).trans
      (lll_inner_eq_cellInner G theta 1 a b).symm
  have hp : PhysicalFermionNormalSquare.pairGramAt G theta R S =
      inner ℂ (rawPlaneJet G theta 0 R) (rawPlaneJet G theta 0 S) *
        inner ℂ (rawPlaneJet G theta 1 R) (rawPlaneJet G theta 1 S) -
      inner ℂ (rawPlaneJet G theta 0 R) (rawPlaneJet G theta 1 S) *
        inner ℂ (rawPlaneJet G theta 1 R) (rawPlaneJet G theta 0 S) := by
    simp only [PhysicalFermionNormalSquare.pairGramAt, physicalJetCoordinates,
      ← map_neg, rawPairGram, hg, inner_neg_left, inner_neg_right, neg_neg]
    ring
  rw [m1Q_gram_finite_sum, hp]
  norm_num [Finset.sum_range_succ, relativeBinomialCoeff]
  linear_combination
    (inner ℂ (rawPlaneJet G theta 0 R) (rawPlaneJet G theta 0 S) *
      inner ℂ (rawPlaneJet G theta 1 R) (rawPlaneJet G theta 1 S) -
      inner ℂ (rawPlaneJet G theta 0 R) (rawPlaneJet G theta 1 S) *
      inner ℂ (rawPlaneJet G theta 1 R) (rawPlaneJet G theta 0 S))/2 * scale_complex_sq

#print axioms m1Q_gram_eq_pairGramAt
#print axioms m1Q_tmul
#print axioms m1Q_normalizedSlater_original_pair
#print axioms m1Q_exchange
#print axioms m1Q_adjoint_antisymmetric
#print axioms m1EvaluationKernel_reproduces
#print axioms m1Q_adjoint_evaluationKernel
#print axioms m1Q_gram_finite_sum
end TorusLean.Shared.FermionM1NearProjection
