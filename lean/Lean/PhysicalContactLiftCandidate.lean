import ContactHilbertBridge
import torus.shared.ContactFrame

/-! Accepted physical leaf: the separate `physical-contact-leaf-receipt.json`
binds its selected source build, full types, standard axiom closure, pinned
Nanoda and trustLevel=0 replay with invalid-proof controls. Its five leaf
roots are included in that 14-root batch, outside the physical 99-root batch.
This bosonic J0 same-Q/same-h occupation bridge does not identify a full
many-body carrier, all-N physical Hamiltonian, or fermionic derivative contact. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace TorusLean.Boson.PhysicalContactLiftCandidate

open TorusLean.Shared
open TorusLean.Boson.UnitaryTransport TorusLean.Boson.Sym2Evaluation
open TorusLean.Boson.ContactHilbertBridge

/-- Coordinates have the actual derived finrank, without assuming it is M. -/
abbrev OrbitalIndex (G : Shared.Geometry) (theta : Shared.Twist) :=
  Fin (Module.finrank ℂ (Shared.LLL G theta 1))

def physicalOrbitalCoordinates (G : Shared.Geometry) (theta : Shared.Twist) :
    Shared.LLL G theta 1 ≃ₗᵢ[ℂ] Orbital (OrbitalIndex G theta) :=
  (stdOrthonormalBasis ℂ (Shared.LLL G theta 1)).repr

/-- Worker namespace only; Shared's physical pair h is unchanged. -/
def contactPairCoordinates (G : Shared.Geometry) (theta : Shared.Twist) :
    TwoBodyLift.PairSpace (OrbitalIndex G theta) →ₗ[ℂ]
      TwoBodyLift.PairSpace (OrbitalIndex G theta) :=
  coordinatePairOperator (physicalOrbitalCoordinates G theta) (Shared.contactQ G theta)

/-- Actual lift of the same root-owned Q†Q, before an N-body function-map identification. -/
def contactCoreHamiltonian (G : Shared.Geometry) (theta : Shared.Twist) :
    Core (OrbitalIndex G theta) ℂ →ₗ[ℂ] Core (OrbitalIndex G theta) ℂ :=
  coordinateHamiltonian (physicalOrbitalCoordinates G theta) (Shared.contactQ G theta)

theorem contactPairCoordinates_inner (G : Shared.Geometry) (theta : Shared.Twist)
    (ψ φ : TwoBodyLift.PairSpace (OrbitalIndex G theta)) :
    inner ℂ ψ (contactPairCoordinates G theta φ) =
      inner ℂ ((sym2Transport (physicalOrbitalCoordinates G theta)).symm ψ)
        (Shared.bosonPairOperator G theta
          ((sym2Transport (physicalOrbitalCoordinates G theta)).symm φ)) := by
  exact coordinatePairOperator_inner (physicalOrbitalCoordinates G theta)
    (Shared.contactQ G theta) ψ φ

theorem contactCoreHamiltonian_nonneg (G : Shared.Geometry) (theta : Shared.Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    0 ≤ (SpectatorControl.ip f (contactCoreHamiltonian G theta f)).re :=
  coordinateHamiltonian_nonneg (physicalOrbitalCoordinates G theta) (Shared.contactQ G theta) f

theorem contactCoreHamiltonian_sector (G : Shared.Geometry) (theta : Shared.Twist)
    (N : ℕ) (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous N) :
    (contactCoreHamiltonian G theta f).IsHomogeneous N :=
  coordinateHamiltonian_sector (physicalOrbitalCoordinates G theta) (Shared.contactQ G theta) N f hf

/-- On the accepted normalized two-particle image, this is the same μ₂ contact form. -/
theorem contactCoreHamiltonian_sym2_cell (G : Shared.Geometry) (theta : Shared.Twist)
    (ψ φ : TwoBodyLift.PairSpace (OrbitalIndex G theta)) :
    SpectatorControl.ip (fockPairMap ψ.val)
      (contactCoreHamiltonian G theta (fockPairMap φ.val)) =
      Shared.cellInner G 2
        (Shared.contactQ G theta ((sym2Transport (physicalOrbitalCoordinates G theta)).symm ψ)).val
        (Shared.contactQ G theta ((sym2Transport (physicalOrbitalCoordinates G theta)).symm φ)).val := by
  rw [contactCoreHamiltonian, coordinateHamiltonian_sym2_inner]
  exact Shared.bosonPairOperator_inner G theta _ _

/-- Derived charge-two evaluation norm, not yet identified with the paper's k₂. -/
theorem rawRieszPair_le_contactCoreHamiltonian (G : Shared.Geometry) (theta : Shared.Twist)
    (R : ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    SpectatorControl.q (modePair
      (physicalOrbitalCoordinates G theta (Shared.evaluationKernel G theta 1 R)) f) ≤
      ‖Shared.lllEvaluation G theta 2 R‖ ^ 2 *
        (SpectatorControl.ip f (contactCoreHamiltonian G theta f)).re := by
  apply coordinate_pair_bound (physicalOrbitalCoordinates G theta) (Shared.contactQ G theta)
    (Shared.lllEvaluation G theta 2 R) (Shared.evaluationKernel G theta 1 R)
  intro ψ
  change (Shared.rawContactQ G theta ψ.val).val R =
    inner ℂ (symTensor (Shared.evaluationKernel G theta 1 R)
      (Shared.evaluationKernel G theta 1 R)).val ψ.val
  have he := Shared.contactQ_evaluation G theta ψ R
  change (Shared.rawContactQ G theta ψ.val).val R =
    inner ℂ (symTensor (Shared.evaluationKernel G theta 1 R)
      (Shared.evaluationKernel G theta 1 R)).val ψ.val at he
  exact he

end TorusLean.Boson.PhysicalContactLiftCandidate
