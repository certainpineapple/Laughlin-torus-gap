import torus.shared.BosonLiftSquare
import torus.shared.PhysicalBosonOperator

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonSquare
open TorusLean.Boson TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonPairContractions TorusLean.Shared.BosonLiftSquare
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonLinearEquiv TorusLean.Shared.PhysicalBosonOperator
open TorusLean.Shared.PhysicalBosonS4Positive TorusLean.Shared.PhysicalBosonS4Coefficients
open TorusLean.Boson.PhysicalContactLiftCandidate
local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- The actual same-Q full-sector Hamiltonian square, with all three CCR
contraction terms retained. This is an exact identity, not a spectral bound. -/
theorem contactCore_square_normal_order (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    contactCoreHamiltonian G theta (contactCoreHamiltonian G theta p) =
      fourBodyCoreOperator G theta p +
        contractionLift (contactPairCoordinates G theta) singleContraction p +
        contractionLift (contactPairCoordinates G theta) doubleContraction p :=
  twoBodyLift_square_normal_order (contactPairCoordinates G theta) p

theorem physical_contact_square_form (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    sectorInner G N f.val
      (transportedContactHamiltonian G theta N (transportedContactHamiltonian G theta N f)).val =
      normalOrderedFourBodyForm G theta ((physicalSectorLinearEquiv G theta N).symm f).val +
        occupationInner (fun _ => 1) ((physicalSectorLinearEquiv G theta N).symm f).val
          (contractionLift (contactPairCoordinates G theta) singleContraction
            ((physicalSectorLinearEquiv G theta N).symm f).val) +
        occupationInner (fun _ => 1) ((physicalSectorLinearEquiv G theta N).symm f).val
          (contractionLift (contactPairCoordinates G theta) doubleContraction
            ((physicalSectorLinearEquiv G theta N).symm f).val) := by
  rw [transportedContactHamiltonian_inner, transportedContactHamiltonian_coordinates]
  change occupationInner (fun _ => 1) _ (contactCoreHamiltonian G theta
    (contactCoreHamiltonian G theta _)) = _
  rw [contactCore_square_normal_order, occupationInner_add_right, occupationInner_add_right,
    fourBodyCoreOperator_inner]

#print axioms contactCore_square_normal_order
#print axioms physical_contact_square_form
end TorusLean.Shared.PhysicalBosonSquare
