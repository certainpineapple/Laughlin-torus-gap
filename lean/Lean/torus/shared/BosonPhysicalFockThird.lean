import torus.shared.BosonPhysicalThird
import torus.shared.ThermalCoherentFockResolventPhysical

/-! Transfer the original uniform sector third to the exact self-adjoint
physical Fock direct sum. The operator domain remains D(H), and the resolvent
is an actual bounded two-sided inverse with its explicit uniform norm bound. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonPhysicalFockThird
open TorusLean.Boson
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonOperator
open TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.BosonPhysicalThird
open TorusLean.Shared.ThermalCoherentFockSector
open TorusLean.Shared.ThermalCoherentFockPhysical
open TorusLean.Shared.ThermalCoherentFockEnergy
open TorusLean.Shared.ThermalCoherentFockResolventPhysical
open TorusLean.Fermion.LatticePacking

theorem physical_sector_third_norm (G : Geometry) (theta : Twist) (M : ℕ)
    (f : PhysicalBosonCarrier G theta M) (hG : 20≤systole G) :
    (1/3:ℝ)*actualParticleContactEnergy G M f.val ≤
      ‖transportedContactHamiltonian G theta M f‖^2 := by
  have he : (sectorInner G M f.val
      (transportedContactHamiltonian G theta M
        (transportedContactHamiltonian G theta M f)).val).re =
        ‖transportedContactHamiltonian G theta M f‖^2 := by
    rw [←transportedContactHamiltonian_symmetric G theta M f
      (transportedContactHamiltonian G theta M f)]
    rw [←physical_inner_eq_sectorInner]
    exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have h := physical_third_systole_twenty G theta M f hG
  rw [he] at h
  simpa only [div_eq_mul_inv,one_div,mul_comm,one_mul] using h

theorem physicalFockHamiltonian_third (G : Geometry) (theta : Twist)
    (hG : 20≤systole G) (x : (physicalFockHamiltonian G theta).domain) :
    (1/3:ℝ)*(inner ℂ x.val (physicalFockHamiltonian G theta x)).re ≤
      ‖physicalFockHamiltonian G theta x‖^2 := by
  exact physicalFockHamiltonian_uniform_form_transfer G theta (1/3)
    (fun N f => physical_sector_third_norm G theta N f hG) x

theorem physicalFockHamiltonian_third_resolvent (G : Geometry) (theta : Twist)
    (hG : 20≤systole G) (lambda : ℝ) (hlambda : 0<lambda) (hlambda' : lambda<1/3) :
    ∃ R : PhysicalFock G theta →L[ℂ] PhysicalFock G theta,
      ‖R‖ ≤ (min lambda (1/3-lambda))⁻¹ ∧
      (∀ y, ∃ hy : R y ∈ (physicalFockHamiltonian G theta).domain,
        physicalFockHamiltonian G theta ⟨R y,hy⟩ - (lambda:ℂ) • R y = y) ∧
      (∀ x : (physicalFockHamiltonian G theta).domain,
        R (physicalFockHamiltonian G theta x - (lambda:ℂ) • x.val) = x.val) := by
  exact physicalFockHamiltonian_bounded_resolvent G theta (1/3) lambda hlambda hlambda'
    (fun N f => physical_sector_third_norm G theta N f hG)

#print axioms physical_sector_third_norm
#print axioms physicalFockHamiltonian_third
#print axioms physicalFockHamiltonian_third_resolvent
end TorusLean.Shared.BosonPhysicalFockThird
