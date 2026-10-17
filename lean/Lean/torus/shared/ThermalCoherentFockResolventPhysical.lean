import torus.shared.ThermalCoherentFockEnergy
import torus.shared.ThermalCoherentFockResolventSum

/-! A genuine uniformly bounded two-sided resolvent for the original physical
Fock operator, conditional only on the explicitly stated original finite-sector
form estimate. This is an inverse theorem, not a newly defined spectral-gap
predicate. The physical finite-sector premise must be discharged separately. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFockResolventPhysical
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonOperator
open TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.ThermalCoherentFockSector TorusLean.Shared.ThermalCoherentFockPhysical
open TorusLean.Shared.ThermalCoherentFockResolventSum

theorem physicalFockHamiltonian_bounded_resolvent (G : Geometry) (theta : Twist)
    (gamma lambda : ℝ) (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hsector : ∀ N (f : PhysicalBosonCarrier G theta N),
      gamma*actualParticleContactEnergy G N f.val ≤ ‖transportedContactHamiltonian G theta N f‖^2) :
    ∃ R : PhysicalFock G theta →L[ℂ] PhysicalFock G theta,
      ‖R‖ ≤ (min lambda (gamma-lambda))⁻¹ ∧
      (∀ y, ∃ hy : R y ∈ (physicalFockHamiltonian G theta).domain,
        physicalFockHamiltonian G theta ⟨R y,hy⟩ - (lambda : ℂ) • R y = y) ∧
      (∀ x : (physicalFockHamiltonian G theta).domain,
        R (physicalFockHamiltonian G theta x - (lambda : ℂ) • x.val) = x.val) := by
  have hf : ∀ N (f : PhysicalBosonCarrier G theta N),
      gamma*(inner ℂ f (actualSectorHamiltonian G theta N f)).re ≤
        ‖actualSectorHamiltonian G theta N f‖^2 := by
    intro N f
    rw [actualSectorHamiltonian_energy,actualSectorHamiltonian_apply]
    exact hsector N f
  refine ⟨directSumResolvent (actualSectorHamiltonian G theta) gamma lambda hlambda hlambda' hf,
    directSumResolvent_norm_le _ _ _ _ _ _,?_,?_⟩
  · intro y
    exact ⟨directSumResolvent_mem_domain _ _ _ _ _ _ y,
      directSumResolvent_right_inverse _ _ _ _ _ _ y⟩
  · intro x
    exact directSumResolvent_left_inverse _ _ _ _ _ _ x

end TorusLean.Shared.ThermalCoherentFockResolventPhysical
