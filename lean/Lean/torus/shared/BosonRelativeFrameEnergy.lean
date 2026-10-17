import torus.shared.BosonRelativeFrameTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonRelativeFrame
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.PhysicalContactLiftCandidate
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonS4 TorusLean.Shared.PhysicalBosonS4Coefficients
open scoped TensorProduct ComplexConjugate BigOperators

local instance energyOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) :=
  ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem doublePairTensor_inner_expansion (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (z : Configuration N) :
    inner ℂ (doublePairTensor G theta N p z) (doublePairTensor G theta N p z) =
      ∑ a : PairIndex G theta, ∑ c : PairIndex G theta,
        ∑ b : PairIndex G theta, ∑ d : PairIndex G theta,
          (conj (coreFunction G theta N (TwoBodyLift.pairRemove c (TwoBodyLift.pairRemove a p)) z) *
            coreFunction G theta N (TwoBodyLift.pairRemove d (TwoBodyLift.pairRemove b p)) z) *
          (TwoBodyLift.pairKernel (contactPairCoordinates G theta) a b *
            TwoBodyLift.pairKernel (contactPairCoordinates G theta) c d) := by
  simp only [doublePairTensor]
  simp only [sum_inner]
  simp only [inner_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  rw [inner_smul_left (pairSection G theta a ⊗ₜ[ℂ] pairSection G theta c)
    ((coreFunction G theta N (TwoBodyLift.pairRemove d (TwoBodyLift.pairRemove b p)) z) •
      (pairSection G theta b ⊗ₜ[ℂ] pairSection G theta d)) _,
    inner_smul_right (pairSection G theta a ⊗ₜ[ℂ] pairSection G theta c)
      (pairSection G theta b ⊗ₜ[ℂ] pairSection G theta d) _,
    TensorProduct.inner_tmul, pairSection_inner, pairSection_inner]
  ring

theorem doublePairTensor_inner_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (fun z => inner ℂ (doublePairTensor G theta N p z)
      (doublePairTensor G theta N p z)) (sectorMeasure G N) := by
  simp_rw [doublePairTensor_inner_expansion]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun c _ =>
    integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun d _ =>
      (coreFunction_cross_integrable G theta N _ _).mul_const _))))

theorem doublePairTensor_normSq_integrable (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (fun z => ‖doublePairTensor G theta N p z‖^2) (sectorMeasure G N) := by
  have h := (doublePairTensor_inner_integrable G theta N p).re
  change Integrable (fun z => (inner ℂ (doublePairTensor G theta N p z)
    (doublePairTensor G theta N p z)).re) (sectorMeasure G N) at h
  have heq : (fun z => ‖doublePairTensor G theta N p z‖^2) =
      (fun z => (inner ℂ (doublePairTensor G theta N p z) (doublePairTensor G theta N p z)).re) :=
    funext (fun z => InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _)
  rw [heq]
  exact h

theorem doublePairTensor_integrated_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous ((N+2)+2)) :
    (∫ z, inner ℂ (doublePairTensor G theta N p z) (doublePairTensor G theta N p z)
      ∂sectorMeasure G N) = normalOrderedFourBodyForm G theta p := by
  classical
  unfold normalOrderedFourBodyForm
  conv_rhs => arg 2; ext a; rw [Finset.sum_comm]
  simp_rw [doublePairTensor_inner_expansion]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun c _ =>
    integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun d _ =>
      (coreFunction_cross_integrable G theta N _ _).mul_const _))))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ (fun b _ =>
    integrable_finsetSum _ (fun d _ => (coreFunction_cross_integrable G theta N _ _).mul_const _)))]
  apply Finset.sum_congr rfl
  intro c _
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun d _ =>
    (coreFunction_cross_integrable G theta N _ _).mul_const _))]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finsetSum _ (fun d _ => (coreFunction_cross_integrable G theta N _ _).mul_const _)]
  apply Finset.sum_congr rfl
  intro d _
  rw [integral_mul_const]
  have ha := TwoBodyLift.pairRemove_sector a (N+2) p hp
  have hb := TwoBodyLift.pairRemove_sector b (N+2) p hp
  have hc := TwoBodyLift.pairRemove_sector c N _ ha
  have hd := TwoBodyLift.pairRemove_sector d N _ hb
  rw [show (∫ z, conj (coreFunction G theta N (TwoBodyLift.pairRemove c
      (TwoBodyLift.pairRemove a p)) z) * coreFunction G theta N (TwoBodyLift.pairRemove d
      (TwoBodyLift.pairRemove b p)) z ∂sectorMeasure G N) =
      occupationInner (fun _ => 1) (TwoBodyLift.pairRemove c (TwoBodyLift.pairRemove a p))
        (TwoBodyLift.pairRemove d (TwoBodyLift.pairRemove b p)) from
      coreFunction_inner G theta N _ _ hc hd]
  ring

theorem doublePairTensor_integrated_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous ((N+2)+2)) :
    (∫ z, ‖doublePairTensor G theta N p z‖^2 ∂sectorMeasure G N) =
      (normalOrderedFourBodyForm G theta p).re := by
  simp_rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [integral_re (doublePairTensor_inner_integrable G theta N p),
    doublePairTensor_integrated_inner G theta N p hp]
  rfl

/-- The full tensor norm, integrated in the original spectator measure,
is exactly the already defined positive four-body form. -/
theorem physicalDoublePairTensor_integrated_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    (∫ z, ‖physicalDoublePairTensor G theta N f z‖^2 ∂sectorMeasure G N) =
      actualPositiveFourBodyForm G theta N f := by
  rw [actual_S4_eq_normalOrderedFourBodyForm]
  exact doublePairTensor_integrated_normSq G theta N _
    ((physicalSectorEquiv G theta ((N+2)+2)).symm f).property

end TorusLean.Shared.BosonRelativeFrame
