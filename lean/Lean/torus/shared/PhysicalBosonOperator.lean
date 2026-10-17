import torus.shared.PhysicalBosonLinearEquiv
import torus.shared.PhysicalBosonFullContact

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PhysicalBosonOperator

open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Boson.ContactHilbertBridge TorusLean.Boson.PhysicalContactLiftCandidate

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) :=
  ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- Restriction of the unchanged same-Q lift to its proved invariant sector. -/
def sectorContactLift (G : Geometry) (theta : Twist) (N : ℕ) :
    MvPolynomial.homogeneousSubmodule (PhysicalBosonSector.OrbitalIndex G theta) ℂ N →ₗ[ℂ]
      MvPolynomial.homogeneousSubmodule (PhysicalBosonSector.OrbitalIndex G theta) ℂ N where
  toFun p := ⟨contactCoreHamiltonian G theta p.val,
    contactCoreHamiltonian_sector G theta N p.val p.property⟩
  map_add' p q := Subtype.ext ((contactCoreHamiltonian G theta).map_add p.val q.val)
  map_smul' c p := Subtype.ext ((contactCoreHamiltonian G theta).map_smul c p.val)

/-- Explicitly transported linear contact operator on the independent full
physical carrier. Its energy is identified with the original particle form below. -/
def transportedContactHamiltonian (G : Geometry) (theta : Twist) (N : ℕ) :
    PhysicalBosonCarrier G theta N →ₗ[ℂ] PhysicalBosonCarrier G theta N :=
  (physicalSectorLinearEquiv G theta N).toLinearMap.comp
    ((sectorContactLift G theta N).comp (physicalSectorLinearEquiv G theta N).symm.toLinearMap)

theorem transportedContactHamiltonian_coordinates (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    (physicalSectorLinearEquiv G theta N).symm (transportedContactHamiltonian G theta N f) =
      sectorContactLift G theta N ((physicalSectorLinearEquiv G theta N).symm f) := by
  exact (physicalSectorLinearEquiv G theta N).symm_apply_apply _

theorem transportedContactHamiltonian_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : PhysicalBosonCarrier G theta N) :
    sectorInner G N f.val (transportedContactHamiltonian G theta N g).val =
      TorusLean.Boson.occupationInner (fun _ => 1)
        ((physicalSectorLinearEquiv G theta N).symm f).val
        (contactCoreHamiltonian G theta ((physicalSectorLinearEquiv G theta N).symm g).val) := by
  have h := physicalSectorEquiv_inner G theta N f (transportedContactHamiltonian G theta N g)
  rw [← physicalSectorLinearEquiv_toEquiv] at h
  change sectorInner G N f.val (transportedContactHamiltonian G theta N g).val =
    TorusLean.Boson.occupationInner (fun _ => 1)
      ((physicalSectorLinearEquiv G theta N).symm f).val
      ((physicalSectorLinearEquiv G theta N).symm (transportedContactHamiltonian G theta N g)).val at h
  rw [transportedContactHamiltonian_coordinates] at h
  exact h

theorem transportedContactHamiltonian_energy (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    (sectorInner G N f.val (transportedContactHamiltonian G theta N f).val).re =
      actualParticleContactEnergy G N f.val := by
  rw [transportedContactHamiltonian_inner]
  have h := TorusLean.Shared.PhysicalBosonFullContact.fullCarrier_contact_energy_same_lift G theta N f
  rw [← physicalSectorLinearEquiv_toEquiv] at h
  exact h.symm

theorem transportedContactHamiltonian_nonneg (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    0 ≤ (sectorInner G N f.val (transportedContactHamiltonian G theta N f).val).re := by
  rw [transportedContactHamiltonian_inner]
  exact contactCoreHamiltonian_nonneg G theta ((physicalSectorLinearEquiv G theta N).symm f).val

theorem contactCore_symmetric (G : Geometry) (theta : Twist)
    (p q : TorusLean.Boson.Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    TorusLean.Boson.occupationInner (fun _ => 1) (contactCoreHamiltonian G theta p) q =
      TorusLean.Boson.occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta q) :=
  TorusLean.Boson.TwoBodyLift.twoBodyLift_symmetric _
    (coordinatePairOperator_positive (physicalOrbitalCoordinates G theta) (contactQ G theta)) p q

theorem transportedContactHamiltonian_symmetric (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : PhysicalBosonCarrier G theta N) :
    sectorInner G N (transportedContactHamiltonian G theta N f).val g.val =
      sectorInner G N f.val (transportedContactHamiltonian G theta N g).val := by
  rw [transportedContactHamiltonian_inner]
  have h := physicalSectorEquiv_inner G theta N (transportedContactHamiltonian G theta N f) g
  rw [← physicalSectorLinearEquiv_toEquiv] at h
  change sectorInner G N (transportedContactHamiltonian G theta N f).val g.val =
    TorusLean.Boson.occupationInner (fun _ => 1)
      ((physicalSectorLinearEquiv G theta N).symm (transportedContactHamiltonian G theta N f)).val
      ((physicalSectorLinearEquiv G theta N).symm g).val at h
  rw [transportedContactHamiltonian_coordinates] at h
  exact h.trans (contactCore_symmetric G theta _ _)

#print axioms transportedContactHamiltonian_coordinates
#print axioms transportedContactHamiltonian_inner
#print axioms transportedContactHamiltonian_energy
#print axioms transportedContactHamiltonian_nonneg
#print axioms contactCore_symmetric
#print axioms transportedContactHamiltonian_symmetric

end TorusLean.Shared.PhysicalBosonOperator
