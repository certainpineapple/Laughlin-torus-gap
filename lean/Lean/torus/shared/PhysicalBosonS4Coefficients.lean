import torus.shared.PhysicalBosonS4

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonS4Coefficients
open scoped ComplexConjugate
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonFullContact TorusLean.Shared.PhysicalBosonAnchor
open TorusLean.Shared.PhysicalBosonS4 TorusLean.Boson.PhysicalContactLiftCandidate
local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem integrated_modePair_linear_inner (G : Geometry) (theta : Twist)
    (K : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ →ₗ[ℂ]
      Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    (∫ R, occupationInner (fun _ => 1) (modePair (evaluationCoordinates G theta R) p)
      (K (modePair (evaluationCoordinates G theta R) p)) ∂cellMeasure G 2) =
      ∑ a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        ∑ b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
          TwoBodyLift.pairKernel (contactPairCoordinates G theta) a b *
            occupationInner (fun _ => 1) (TwoBodyLift.pairRemove a p)
              (K (TwoBodyLift.pairRemove b p)) := by
  classical
  simp_rw [modePair_linear_inner_expansion]
  rw [integral_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun b _ => pairProduct_cross_integrable G theta a b _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum Finset.univ (fun b _ => pairProduct_cross_integrable G theta a b _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_mul_const, contactPairKernel_actual]
  rfl

theorem contactCore_cross_expansion (G : Geometry) (theta : Twist)
    (p q : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta q) =
      ∑ a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        ∑ b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
          TwoBodyLift.pairKernel (contactPairCoordinates G theta) a b *
            occupationInner (fun _ => 1) (TwoBodyLift.pairRemove a p)
              (TwoBodyLift.pairRemove b q) := by
  change SpectatorControl.ip p (TwoBodyLift.twoBodyLift (contactPairCoordinates G theta) q) = _
  simp only [TwoBodyLift.twoBodyLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, TwoBodyLift.inner_sum_right, TwoBodyLift.inner_smul_right,
    TwoBodyLift.pairCreate_remove_adjoint, SpectatorControl.ip]

/-- The explicit four-removal, zero-contraction coefficient form for the same
physical pair kernel. This definition does not assert the full H-square expansion. -/
def normalOrderedFourBodyForm (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) : ℂ :=
  ∑ a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
    ∑ b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
      ∑ c : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        ∑ d : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
          TwoBodyLift.pairKernel (contactPairCoordinates G theta) a b *
            TwoBodyLift.pairKernel (contactPairCoordinates G theta) c d *
              occupationInner (fun _ => 1)
                (TwoBodyLift.pairRemove c (TwoBodyLift.pairRemove a p))
                (TwoBodyLift.pairRemove d (TwoBodyLift.pairRemove b p))

theorem integrated_output_energy_coefficients (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    (∫ R, occupationInner (fun _ => 1) (modePair (evaluationCoordinates G theta R) p)
      (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R) p))
      ∂cellMeasure G 2) = normalOrderedFourBodyForm G theta p := by
  rw [integrated_modePair_linear_inner]
  simp_rw [contactCore_cross_expansion]
  simp only [normalOrderedFourBodyForm, Finset.mul_sum, mul_assoc]

theorem actual_S4_eq_normalOrderedFourBodyForm (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    actualPositiveFourBodyForm G theta N f =
      (normalOrderedFourBodyForm G theta
        ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val).re := by
  rw [← physical_output_energy_anchor_S4]
  simp_rw [fullCarrier_contact_energy_same_lift, physicalPairSection_coordinates]
  have h := integral_re (modePair_linear_inner_integrable G theta (contactCoreHamiltonian G theta)
    ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val)
  change (∫ R, (occupationInner (fun _ => 1)
    (modePair (evaluationCoordinates G theta R) ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val)
    (contactCoreHamiltonian G theta (modePair (evaluationCoordinates G theta R)
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val))).re ∂cellMeasure G 2) = _ at h
  exact h.trans (congrArg Complex.re (integrated_output_energy_coefficients G theta _))

#print axioms integrated_modePair_linear_inner
#print axioms contactCore_cross_expansion
#print axioms integrated_output_energy_coefficients
#print axioms actual_S4_eq_normalOrderedFourBodyForm
end TorusLean.Shared.PhysicalBosonS4Coefficients
