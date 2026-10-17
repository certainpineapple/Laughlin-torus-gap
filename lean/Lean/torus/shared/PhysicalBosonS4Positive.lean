import torus.shared.PhysicalBosonS4Coefficients

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonS4Positive
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonAnchor
open TorusLean.Shared.PhysicalBosonS4Coefficients TorusLean.Boson.PhysicalContactLiftCandidate
local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- The explicit normal-ordered four-body operator on the finite occupation
core. All coefficients are the original physical contact pair kernel. -/
def fourBodyCoreOperator (G : Geometry) (theta : Twist) :
    Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ →ₗ[ℂ]
      Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ :=
  ∑ a : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
    ∑ b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
      ∑ c : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
        ∑ d : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta),
          (TwoBodyLift.pairKernel (contactPairCoordinates G theta) a b *
            TwoBodyLift.pairKernel (contactPairCoordinates G theta) c d) •
              (TwoBodyLift.pairCreate a).comp ((TwoBodyLift.pairCreate c).comp
                ((TwoBodyLift.pairRemove d).comp (TwoBodyLift.pairRemove b)))

theorem fourBodyCoreOperator_inner (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    occupationInner (fun _ => 1) p (fourBodyCoreOperator G theta p) =
      normalOrderedFourBodyForm G theta p := by
  change SpectatorControl.ip p _ = _
  simp only [fourBodyCoreOperator, normalOrderedFourBodyForm, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, TwoBodyLift.inner_sum_right,
    TwoBodyLift.inner_smul_right, TwoBodyLift.pairCreate_remove_adjoint, SpectatorControl.ip]

theorem normalOrderedFourBodyForm_nonneg (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    0 ≤ (normalOrderedFourBodyForm G theta p).re := by
  have h := integral_re (modePair_linear_inner_integrable G theta (contactCoreHamiltonian G theta) p)
  rw [integrated_output_energy_coefficients] at h
  change 0 ≤ RCLike.re (normalOrderedFourBodyForm G theta p)
  rw [← h]
  exact integral_nonneg (fun R => contactCoreHamiltonian_nonneg G theta _)

theorem fourBodyCoreOperator_nonneg (G : Geometry) (theta : Twist)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    0 ≤ (occupationInner (fun _ => 1) p (fourBodyCoreOperator G theta p)).re := by
  rw [fourBodyCoreOperator_inner]
  exact normalOrderedFourBodyForm_nonneg G theta p

theorem double_pairRemove_low_sector (G : Geometry) (theta : Twist)
    (a b : TwoBodyLift.PairIndex (PhysicalBosonSector.OrbitalIndex G theta))
    (M : ℕ) (hM : M < 4) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous M) :
    TwoBodyLift.pairRemove a (TwoBodyLift.pairRemove b p) = 0 := by
  by_cases hM2 : M < 2
  · rw [TwoBodyLift.pairRemove_low_sector b M hM2 p hp, map_zero]
  · have hge : 2 ≤ M := Nat.le_of_not_gt hM2
    apply TwoBodyLift.pairRemove_low_sector a (M-2) (by omega)
    apply TwoBodyLift.pairRemove_sector b (M-2) p
    simpa only [Nat.sub_add_cancel hge] using hp

theorem fourBodyCoreOperator_low_sector (G : Geometry) (theta : Twist)
    (M : ℕ) (hM : M < 4) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous M) : fourBodyCoreOperator G theta p = 0 := by
  simp only [fourBodyCoreOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, double_pairRemove_low_sector G theta _ _ M hM p hp,
    map_zero, smul_zero, Finset.sum_const_zero]

#print axioms fourBodyCoreOperator_inner
#print axioms normalOrderedFourBodyForm_nonneg
#print axioms fourBodyCoreOperator_nonneg
#print axioms double_pairRemove_low_sector
#print axioms fourBodyCoreOperator_low_sector
end TorusLean.Shared.PhysicalBosonS4Positive
