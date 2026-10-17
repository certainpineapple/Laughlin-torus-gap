import torus.shared.PhysicalBosonPairBudget

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PhysicalBosonAnchor
open scoped ComplexConjugate

open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonFullContact
open TorusLean.Shared.PhysicalBosonPairBudget TorusLean.Boson.PhysicalContactLiftCandidate

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) :=
  ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- The actual normalized literal pair restriction is a full physical output state. -/
def physicalPairSection (G : Geometry) (theta : Twist) (N : ℕ)
    (R : ℂ) (f : PhysicalBosonCarrier G theta (N+2)) : PhysicalBosonCarrier G theta N :=
  sectorPhysical G theta N ⟨modePair (evaluationCoordinates G theta R)
    ((physicalSectorEquiv G theta (N+2)).symm f).val,
    modePair_sector _ N _ ((physicalSectorEquiv G theta (N+2)).symm f).property⟩

theorem physicalPairSection_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (R : ℂ) (f : PhysicalBosonCarrier G theta (N+2)) :
    (physicalPairSection G theta N R f).val = physicalPairFunction G theta N R f :=
  (physicalPairFunction_eq_core G theta N R f).symm

theorem physicalPairSection_coordinates (G : Geometry) (theta : Twist) (N : ℕ)
    (R : ℂ) (f : PhysicalBosonCarrier G theta (N+2)) :
    ((physicalSectorEquiv G theta N).symm (physicalPairSection G theta N R f)).val =
      modePair (evaluationCoordinates G theta R)
        ((physicalSectorEquiv G theta (N+2)).symm f).val := by
  exact congrArg Subtype.val ((physicalSectorEquiv G theta N).symm_apply_apply _)

theorem modePair_normSq_integrable (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (fun R => occupationMetricNormSq (fun _ => 1)
      (modePair (evaluationCoordinates G theta R) p)) (cellMeasure G 2) := by
  classical
  have h : Integrable (fun R => occupationInner (fun _ => 1)
      (modePair (evaluationCoordinates G theta R) p)
      (modePair (evaluationCoordinates G theta R) p)) (cellMeasure G 2) := by
    simp_rw [modePair_evaluation_inner_expansion]
    exact integrable_finsetSum Finset.univ (fun a _ =>
      integrable_finsetSum Finset.univ (fun b _ => pairProduct_cross_integrable G theta a b _))
  have hr := h.re
  change Integrable (fun R => (occupationInner (fun _ => 1)
    (modePair (evaluationCoordinates G theta R) p)
    (modePair (evaluationCoordinates G theta R) p)).re) (cellMeasure G 2) at hr
  simpa only [occupationInner_self, Complex.ofReal_re] using hr

theorem physicalPair_normSq_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta (N+2)) :
    Integrable (fun R => ∫ z, ‖physicalPairFunction G theta N R f z‖^2
      ∂sectorMeasure G N) (cellMeasure G 2) := by
  simp_rw [physicalPairFunction_normSq]
  exact modePair_normSq_integrable G theta _

/-- The actual pair anchor is exactly the original full-carrier particle
contact energy, with original mu2 anchor measure and mu1^N spectator measure. -/
theorem physical_pair_anchor_energy (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta (N+2)) :
    (∫ R, (∫ z, ‖physicalPairFunction G theta N R f z‖^2 ∂sectorMeasure G N)
      ∂cellMeasure G 2) = actualParticleContactEnergy G (N+2) f.val := by
  simp_rw [physicalPairFunction_normSq]
  rw [integrated_modePair_normSq_same_lift]
  exact (fullCarrier_contact_energy_same_lift G theta (N+2) f).symm

/-- Finite exact cross expansion for any fixed core linear operator. -/
theorem modePair_linear_inner_expansion (G : Geometry) (theta : Twist)
    (K : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ →ₗ[ℂ]
      Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (R : ℂ) :
    occupationInner (fun _ => 1) (modePair (evaluationCoordinates G theta R) p)
      (K (modePair (evaluationCoordinates G theta R) p)) =
      ∑ a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        ∑ b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
          conj (TorusLean.Shared.PhysicalBosonDiagonal.pairProduct G theta a.1 a.2 R) *
            TorusLean.Shared.PhysicalBosonDiagonal.pairProduct G theta b.1 b.2 R *
            occupationInner (fun _ => 1) (TwoBodyLift.pairRemove a p) (K (TwoBodyLift.pairRemove b p)) := by
  classical
  rw [modePair_evaluation_expansion]
  simp only [map_sum, map_smul]
  change SpectatorControl.ip _ _ = _
  simp only [TwoBodyLift.inner_sum_left, TwoBodyLift.inner_sum_right,
    TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right, Complex.star_def,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [SpectatorControl.ip]
  ring

theorem modePair_linear_inner_integrable (G : Geometry) (theta : Twist)
    (K : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ →ₗ[ℂ]
      Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (fun R => occupationInner (fun _ => 1)
      (modePair (evaluationCoordinates G theta R) p)
      (K (modePair (evaluationCoordinates G theta R) p))) (cellMeasure G 2) := by
  classical
  simp_rw [modePair_linear_inner_expansion]
  exact integrable_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun b _ => pairProduct_cross_integrable G theta a b _))

/-- The output contact energy is genuinely integrable in the anchor, rather
than a formal Bochner integral with an unproved domain assumption. -/
theorem physicalPair_output_energy_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta (N+2)) :
    Integrable (fun R => actualParticleContactEnergy G N
      (physicalPairSection G theta N R f).val) (cellMeasure G 2) := by
  simp_rw [fullCarrier_contact_energy_same_lift, physicalPairSection_coordinates]
  exact (modePair_linear_inner_integrable G theta (contactCoreHamiltonian G theta) _).re

#print axioms physicalPairSection_apply
#print axioms physicalPairSection_coordinates
#print axioms modePair_normSq_integrable
#print axioms physicalPair_normSq_integrable
#print axioms physical_pair_anchor_energy
#print axioms modePair_linear_inner_expansion
#print axioms modePair_linear_inner_integrable
#print axioms physicalPair_output_energy_integrable

end TorusLean.Shared.PhysicalBosonAnchor
