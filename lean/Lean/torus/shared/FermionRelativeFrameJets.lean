import torus.shared.FermionRelativeFrameTensor
import torus.shared.ChargeTwoEvaluation

/-! Relative-jet evaluation on the actual fermion spectator tensor.  The
charge-two descendants below are genuine canonical derivative evaluations.
Identification of their single-particle-jet coefficients with eq:F-pair is
a separate obligation; this file does not assume or claim that identification.
The relative index is d throughout, never the shifted orbital total d+1. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionRelativeFrame
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionExterior
open TorusLean.Shared.PhysicalFermionPairContraction TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.ChargeTwoEvaluation
open TorusLean.Shared.ChargeTwoIsometry
open scoped TensorProduct ComplexConjugate BigOperators

/-- Canonical COM derivative of the original true charge-two CAR amplitude. -/
def pairDescendant (G : Geometry) (theta : Twist) (d : ℕ) (R : ℂ) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  ∑ a : PairIndex G theta, chargeTwoJetEvaluation G theta d R (pairSection G theta a) •
    modePairAnnihilate (physicalQ G theta) a

def exteriorPairDescendant (G : Geometry) (theta : Twist) (N d : ℕ) (R : ℂ) :
    Exterior (Fin (physicalQ G theta+1)) (N+2) →ₗ[ℂ]
      Exterior (Fin (physicalQ G theta+1)) N :=
  ∑ a : PairIndex G theta, chargeTwoJetEvaluation G theta d R (pairSection G theta a) •
    exteriorModePair G theta N a

@[simp] theorem exteriorPairDescendant_coe (G : Geometry) (theta : Twist) (N d : ℕ) (R : ℂ)
    (x : Exterior (Fin (physicalQ G theta+1)) (N+2)) :
    (exteriorPairDescendant G theta N d R x : Space (physicalQ G theta)) =
      pairDescendant G theta d R (x : Space (physicalQ G theta)) := by
  simp only [exteriorPairDescendant, pairDescendant, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul, exteriorModePair_coe]

lemma chargeTwoJetEvaluation_zero_apply (G : Geometry) (theta : Twist) (R : ℂ)
    (f : LLL G theta 2) : chargeTwoJetEvaluation G theta 0 R f = f.val R := by
  rw [chargeTwoJetEvaluation, ContinuousLinearMap.comp_apply, canonicalJetEvaluation_zero]
  have h := evaluation_scaling G theta R ((scalingLinearIsometryEquiv G theta).symm f)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

@[simp] theorem pairDescendant_zero (G : Geometry) (theta : Twist) (R : ℂ) :
    pairDescendant G theta 0 R = pairAt G theta R := by
  rw [pairAt_section_expansion]
  simp only [pairDescendant, chargeTwoJetEvaluation_zero_apply]

theorem pairDescendant_commute (G : Geometry) (theta : Twist) (d e : ℕ) (R S : ℂ) :
    pairDescendant G theta d R * pairDescendant G theta e S =
      pairDescendant G theta e S * pairDescendant G theta d R := by
  simp only [pairDescendant, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show modePairAnnihilate (physicalQ G theta) a * modePairAnnihilate (physicalQ G theta) b =
    modePairAnnihilate (physicalQ G theta) b * modePairAnnihilate (physicalQ G theta) a from
    rawPairAnnihilate_commute _ _ _ _ _, mul_comm]

theorem exteriorPairDescendant_commute (G : Geometry) (theta : Twist) (N d e : ℕ) (R S : ℂ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    exteriorPairDescendant G theta N d R (exteriorPairDescendant G theta (N+2) e S x) =
      exteriorPairDescendant G theta N e S (exteriorPairDescendant G theta (N+2) d R x) := by
  apply Subtype.ext
  simp only [exteriorPairDescendant_coe]
  exact LinearMap.congr_fun (pairDescendant_commute G theta d e R S) x

/-- The exact relative-binomial C_d combination in the original ordering.
This becomes paper eq:F-Cd after the independent B_p coefficient identity. -/
def fourBodyJet (G : Geometry) (theta : Twist) (d : ℕ) (R : ℂ) :
    Module.End ℂ (Space (physicalQ G theta)) :=
  ∑ p ∈ Finset.range (d+1), relativeBinomialCoeff d p •
    (pairDescendant G theta p R * pairDescendant G theta (d-p) R)

def exteriorFourBodyJet (G : Geometry) (theta : Twist) (N d : ℕ) (R : ℂ) :
    Exterior (Fin (physicalQ G theta+1)) ((N+2)+2) →ₗ[ℂ]
      Exterior (Fin (physicalQ G theta+1)) N :=
  ∑ p ∈ Finset.range (d+1), relativeBinomialCoeff d p •
    (exteriorPairDescendant G theta N p R).comp
      (exteriorPairDescendant G theta (N+2) (d-p) R)

@[simp] theorem exteriorFourBodyJet_coe (G : Geometry) (theta : Twist) (N d : ℕ) (R : ℂ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    (exteriorFourBodyJet G theta N d R x : Space (physicalQ G theta)) =
      fourBodyJet G theta d R (x : Space (physicalQ G theta)) := by
  simp only [exteriorFourBodyJet, fourBodyJet, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Module.End.mul_apply, Submodule.coe_sum, Submodule.coe_smul,
    exteriorPairDescendant_coe]

lemma pairDescendant_pair_spectator (G : Geometry) (theta : Twist) (N d e : ℕ) (R S : ℂ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) (z : Configuration N) :
    physicalExteriorLinear G theta N
      (exteriorPairDescendant G theta N e S (exteriorPairDescendant G theta (N+2) d R x)) z =
      ∑ a : PairIndex G theta, ∑ b : PairIndex G theta,
        chargeTwoJetEvaluation G theta d R (pairSection G theta a) *
        chargeTwoJetEvaluation G theta e S (pairSection G theta b) * doubleSpectator G theta N x a b z := by
  simp only [exteriorPairDescendant, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    doubleSpectator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- J_d on the full true two-anchor tensor is the C_d derivative combination,
including all points and every remaining physical spectator. -/
theorem relativeJet_doublePairTensor (G : Geometry) (theta : Twist) (N d : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) (z : Configuration N) (R : ℂ) :
    (relativeJet G theta 2 2 d (doublePairTensor G theta N x z)).val R =
      physicalExteriorLinear G theta N (exteriorFourBodyJet G theta N d R x) z := by
  change lllEvaluation G theta 4 R
    (relativeJet G theta 2 2 d (doublePairTensor G theta N x z)) = _
  simp only [doublePairTensor, map_sum, map_smul, smul_eq_mul, lllEvaluation_apply]
  simp_rw [relativeJet_tmul_leibniz]
  simp only [Finset.mul_sum]
  unfold exteriorFourBodyJet
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
    map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hcomm (p : ℕ) :
      exteriorPairDescendant G theta N p R (exteriorPairDescendant G theta (N+2) (d-p) R x) =
      exteriorPairDescendant G theta N (d-p) R (exteriorPairDescendant G theta (N+2) p R x) :=
    exteriorPairDescendant_commute G theta N p (d-p) R R x
  simp_rw [hcomm, pairDescendant_pair_spectator G theta N]
  simp only [Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Spectator Parseval has no multiplicity depending on the remaining N. -/
theorem fourBodyJet_spectator_normSq (G : Geometry) (theta : Twist) (N d : ℕ) (R : ℂ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    (∫ z, ‖(relativeJet G theta 2 2 d (doublePairTensor G theta N x z)).val R‖^2
      ∂sectorMeasure G N) = occupationNormSq (physicalQ G theta) (fourBodyJet G theta d R x) := by
  simp_rw [relativeJet_doublePairTensor]
  have h := physicalExteriorEquiv_normSq G theta N (exteriorFourBodyJet G theta N d R x)
  rw [exteriorFourBodyJet_coe] at h
  exact h

#print axioms pairDescendant_zero
#print axioms pairDescendant_commute
#print axioms relativeJet_doublePairTensor
#print axioms fourBodyJet_spectator_normSq
end TorusLean.Shared.FermionRelativeFrame
