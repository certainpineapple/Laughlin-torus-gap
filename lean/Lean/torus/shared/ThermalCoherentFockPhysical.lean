import torus.shared.ThermalCoherentFockSector
import torus.shared.ThermalCoherentFockGraph

/-! The actual bosonic Fock space and its self-adjoint contact Hamiltonian.
Geometry, flux and twist remain fixed while only the particle index varies.
No filling-dependent Laughlin-kernel dimension is asserted for this sum. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFockPhysical
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonOperator
open TorusLean.Shared.ThermalCoherentFockSector
open TorusLean.Shared.ThermalCoherentFockDirectSum TorusLean.Shared.ThermalCoherentFockGraph

abbrev PhysicalFock (G : Geometry) (theta : Twist) := lp (PhysicalBosonCarrier G theta) 2

def physicalFockHamiltonian (G : Geometry) (theta : Twist) :
    PhysicalFock G theta →ₗ.[ℂ] PhysicalFock G theta :=
  blockDirectSum (actualSectorHamiltonian G theta)

theorem physicalFockHamiltonian_domain (G : Geometry) (theta : Twist)
    (x : PhysicalFock G theta) :
    x ∈ (physicalFockHamiltonian G theta).domain ↔
      Summable (fun N => ‖transportedContactHamiltonian G theta N (x N)‖^2) :=
  mem_blockDomain_iff (actualSectorHamiltonian G theta) x

theorem physicalFockHamiltonian_apply (G : Geometry) (theta : Twist)
    (x : (physicalFockHamiltonian G theta).domain) (N : ℕ) :
    physicalFockHamiltonian G theta x N = transportedContactHamiltonian G theta N (x.val N) := rfl

theorem physicalFockHamiltonian_selfAdjoint (G : Geometry) (theta : Twist) :
    IsSelfAdjoint (physicalFockHamiltonian G theta) :=
  blockDirectSum_selfAdjoint (actualSectorHamiltonian G theta)
    (actualSectorHamiltonian_selfAdjoint G theta)

theorem physicalFockHamiltonian_has_finiteParticleCore (G : Geometry) (theta : Twist) :
    (physicalFockHamiltonian G theta).HasCore finiteParticleCore :=
  blockDirectSum_has_finiteParticleCore (actualSectorHamiltonian G theta)
    (actualSectorHamiltonian_selfAdjoint G theta)

end TorusLean.Shared.ThermalCoherentFockPhysical
