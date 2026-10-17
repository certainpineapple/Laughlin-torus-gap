import torus.shared.PhysicalBosonMembership
import torus.shared.PhysicalBosonContactForm

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PhysicalBosonFullContact

open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Boson.PhysicalContactLiftCandidate

/-- Every independently defined full physical boson state has the SAME
actual particle-pair contact quadratic form as the unchanged occupation lift.
This is an all-N quadratic-form identity, not a new operator/gap assertion. -/
theorem fullCarrier_contact_energy_same_lift (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    actualParticleContactEnergy G N f.val =
      (TorusLean.Boson.occupationInner (fun _ => 1)
        ((physicalSectorEquiv G theta N).symm f).val
        (contactCoreHamiltonian G theta ((physicalSectorEquiv G theta N).symm f).val)).re := by
  let p := (physicalSectorEquiv G theta N).symm f
  have hp : coreFunction G theta N p.val = f.val :=
    congrArg Subtype.val ((physicalSectorEquiv G theta N).apply_symm_apply f)
  rw [← hp]
  exact actualParticleContactEnergy_same_lift G theta N p.val p.property

#print axioms fullCarrier_contact_energy_same_lift

end TorusLean.Shared.PhysicalBosonFullContact
