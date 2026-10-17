import torus.shared.PhysicalBosonS4Coefficients
import torus.shared.RelativeJetMapKernel

/-!
Actual spectator-valued two-anchor tensors for the original normalized
bosonic double pair restriction. Coefficients are derived from the existing
finite pair-removal expansion; no tensor carrier or S4 identity is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonRelativeFrame
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.Sym2Evaluation TorusLean.Boson.PhysicalContactLiftCandidate
open TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonPolarization TorusLean.Shared.PhysicalBosonPairBudget
open TorusLean.Shared.PhysicalBosonAnchor TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.PhysicalBosonS4Coefficients
open TorusLean.Shared.RelativeJetMap
open scoped TensorProduct ComplexConjugate BigOperators

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) :=
  ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

abbrev PairIndex (G : Geometry) (theta : Twist) :=
  TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta)

/-- The actual charge2 section of an ordered orbital pair, with the same
normalization as the existing physical contact map. -/
def pairSection (G : Geometry) (theta : Twist) (a : PairIndex G theta) : LLL G theta 2 :=
  contactQ G theta (symTensor (orbitalBasis G theta a.1) (orbitalBasis G theta a.2))

@[simp] theorem pairSection_apply (G : Geometry) (theta : Twist)
    (a : PairIndex G theta) (R : ℂ) :
    (pairSection G theta a).val R = pairProduct G theta a.1 a.2 R :=
  congrFun (contactQ_basis_symTensor G theta a.1 a.2) R

theorem pairSection_inner (G : Geometry) (theta : Twist) (a b : PairIndex G theta) :
    inner ℂ (pairSection G theta a) (pairSection G theta b) =
      TwoBodyLift.pairKernel (contactPairCoordinates G theta) a b := by
  rw [lll_inner_eq_cellInner, contactPairKernel_actual]
  congr 1 <;> funext R <;> exact pairSection_apply G theta _ R

/-- For each actual spectator configuration, a finite tensor in the full
two-charge2 Hilbert space. Both pair-removal normalizations are inherited. -/
def doublePairTensor (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (z : Configuration N) :
    LLL G theta 2 ⊗[ℂ] LLL G theta 2 :=
  ∑ a : PairIndex G theta, ∑ b : PairIndex G theta,
    coreFunction G theta N (TwoBodyLift.pairRemove b (TwoBodyLift.pairRemove a p)) z •
      (pairSection G theta a ⊗ₜ[ℂ] pairSection G theta b)

/-- Every anchor point is represented by this true tensor. -/
theorem doublePairTensor_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (z : Configuration N) (R S : ℂ) :
    rawPairFunction G theta 2 2 (doublePairTensor G theta N p z) (R,S) =
      ∑ a : PairIndex G theta, ∑ b : PairIndex G theta,
        pairProduct G theta a.1 a.2 R * pairProduct G theta b.1 b.2 S *
          coreFunction G theta N (TwoBodyLift.pairRemove b (TwoBodyLift.pairRemove a p)) z := by
  simp only [doublePairTensor, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [rawPairFunction_tmul_apply G theta 2 2 (pairSection G theta a)
    (pairSection G theta b) (R,S), pairSection_apply, pairSection_apply]
  ring

/-- The full tensor's cover function equals the existing two actual B0
pair annihilations, retaining arbitrary finite core and all spectators. -/
theorem doublePairTensor_eq_core (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (z : Configuration N) (R S : ℂ) :
    rawPairFunction G theta 2 2 (doublePairTensor G theta N p z) (R,S) =
      coreFunction G theta N (modePair (evaluationCoordinates G theta S)
        (modePair (evaluationCoordinates G theta R) p)) z := by
  rw [doublePairTensor_apply, modePair_evaluation_expansion G theta R]
  simp only [map_sum, map_smul]
  simp_rw [modePair_evaluation_expansion G theta S]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem physicalDoublePairFunction_eq_core (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (R S : ℂ) (z : Configuration N) :
    physicalDoublePairFunction G theta N R S f z =
      coreFunction G theta N (modePair (evaluationCoordinates G theta S)
        (modePair (evaluationCoordinates G theta R)
          ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val)) z := by
  rw [physicalDoublePairFunction_eq_iterated, physicalPairFunction_eq_core,
    physicalPairSection_coordinates]

/-- The original full independent physical state is passed through its
already proved sector equivalence, never defined by a new coefficient image. -/
def physicalDoublePairTensor (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (z : Configuration N) :
    LLL G theta 2 ⊗[ℂ] LLL G theta 2 :=
  doublePairTensor G theta N ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val z

/-- Literal double restriction, with its original two inverse pair factors,
is the cover function of the constructed full tensor at all points. -/
theorem physicalDoublePairTensor_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (z : Configuration N) (R S : ℂ) :
    rawPairFunction G theta 2 2 (physicalDoublePairTensor G theta N f z) (R,S) =
      physicalDoublePairFunction G theta N R S f z := by
  rw [physicalDoublePairTensor, doublePairTensor_eq_core, physicalDoublePairFunction_eq_core]

end TorusLean.Shared.BosonRelativeFrame
