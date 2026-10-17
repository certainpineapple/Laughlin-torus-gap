import torus.shared.ThermalCoherentFockPhysical

/-! The original physical contact energies on the exact direct-sum domain.
Absolute summability and positivity are conclusions. The uniform sector
estimate remains explicit until the finite-particle gap is independently
closed; no assertion about the unbounded spectrum is made here. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFockEnergy
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonOperator
open TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.ThermalCoherentFockSector
open TorusLean.Shared.ThermalCoherentFockDirectSum TorusLean.Shared.ThermalCoherentFockGraph
open TorusLean.Shared.ThermalCoherentFockPhysical TorusLean.BosonBridge

/-- The original contact energies, with their original measure and all particle
sectors, form the actual direct-sum pairing. -/
theorem physicalFockHamiltonian_energy_hasSum (G : Geometry) (theta : Twist)
    (x : (physicalFockHamiltonian G theta).domain) :
    HasSum (fun N => actualParticleContactEnergy G N (x.val N).val)
      (inner ℂ x.val (physicalFockHamiltonian G theta x)).re := by
  have h := Complex.hasSum_re (lp.hasSum_inner x.val (physicalFockHamiltonian G theta x))
  apply h.congr_fun
  intro N
  exact (actualSectorHamiltonian_energy G theta N (x.val N)).symm

/-- Absolute energy summability follows from the true graph domain, without a
uniform bound on the norms of the particle-sector Hamiltonians. -/
theorem physicalFockHamiltonian_energy_abs_summable (G : Geometry) (theta : Twist)
    (x : (physicalFockHamiltonian G theta).domain) :
    Summable (fun N => |actualParticleContactEnergy G N (x.val N).val|) := by
  have hx := (blockDomain_iff_coordinate_graph (actualSectorHamiltonian G theta) x.val).mp x.property
  have h := sectorEnergy_abs_summable (actualSectorHamiltonian G theta) x.val hx
  apply h.congr
  intro N
  exact congrArg abs (actualSectorHamiltonian_energy G theta N (x.val N))

/-- Positivity holds on the entire operator domain, not only finite-particle vectors. -/
theorem physicalFockHamiltonian_nonneg (G : Geometry) (theta : Twist)
    (x : (physicalFockHamiltonian G theta).domain) :
    0 ≤ (inner ℂ x.val (physicalFockHamiltonian G theta x)).re := by
  apply (physicalFockHamiltonian_energy_hasSum G theta x).nonneg
  intro N
  exact (actualSectorHamiltonian_energy G theta N (x.val N)) ▸
    actualSectorHamiltonian_nonneg G theta N (x.val N)

/-- The precise full-domain form transfer. The hypothesis is the unchanged
physical finite-sector estimate; no domain of H squared is imposed. -/
theorem physicalFockHamiltonian_uniform_form_transfer (G : Geometry) (theta : Twist)
    (γ : ℝ)
    (hsector : ∀ N (f : PhysicalBosonCarrier G theta N),
      γ*actualParticleContactEnergy G N f.val ≤ ‖transportedContactHamiltonian G theta N f‖^2)
    (x : (physicalFockHamiltonian G theta).domain) :
    γ*(inner ℂ x.val (physicalFockHamiltonian G theta x)).re ≤
      ‖physicalFockHamiltonian G theta x‖^2 := by
  apply directSum_uniform_form_transfer (actualSectorHamiltonian G theta) γ ?_ x
  intro N f
  rw [actualSectorHamiltonian_energy,actualSectorHamiltonian_apply]
  exact hsector N f

end TorusLean.Shared.ThermalCoherentFockEnergy
