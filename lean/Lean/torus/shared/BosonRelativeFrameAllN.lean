import torus.shared.BosonRelativeFramePhysical
import torus.shared.PhysicalBosonS4Positive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonRelativeFrame
open MeasureTheory TorusLean.Boson
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4Positive
open TorusLean.Shared.PhysicalBosonS4Coefficients TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Fermion.LatticePacking
open scoped BigOperators

local instance physicalOrbitalIndex_allN_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) :=
  ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem fourBodyJet_low_sector (G : Geometry) (theta : Twist) (M d : ℕ)
    (hM : M < 4) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous M) (R : ℂ) : fourBodyJet G theta d R p = 0 := by
  simp only [fourBodyJet, pairDescendant, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, map_sum, map_smul,
    double_pairRemove_low_sector G theta _ _ M hM p hp, smul_zero, Finset.sum_const_zero]

def coreFourJetEnergy (G : Geometry) (theta : Twist) (D : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, ∑ d : Fin (D+1), occupationMetricNormSq (fun _ => 1)
    (fourBodyJet G theta d.val R p) ∂cellMeasure G 4

theorem coreFourJetEnergy_low_sector (G : Geometry) (theta : Twist) (M D : ℕ)
    (hM : M < 4) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous M) : coreFourJetEnergy G theta D p = 0 := by
  simp [coreFourJetEnergy, fourBodyJet_low_sector G theta M _ hM p hp,
    occupationMetricNormSq]

/-- All particle numbers, including the four zero-output low sectors,
with the same normal-ordered S4 form occurring in the actual H square. -/
theorem coreFourJetEnergy_le_S4 (G : Geometry) (theta : Twist) (M D : ℕ)
    (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (hp : p.IsHomogeneous M) :
    coreFourJetEnergy G theta D p ≤ (1+allowance) * (normalOrderedFourBodyForm G theta p).re := by
  by_cases hM : M < 4
  · rw [coreFourJetEnergy_low_sector G theta M D hM p hp]
    exact mul_nonneg (by unfold allowance; norm_num) (normalOrderedFourBodyForm_nonneg G theta p)
  · have hm : M = ((M-4)+2)+2 := by omega
    have hp' : p.IsHomogeneous ((M-4+2)+2) := hm ▸ hp
    let f := sectorPhysical G theta ((M-4+2)+2) ⟨p,hp'⟩
    have h := physicalFourJetEnergy_le_S4 G theta (M-4) D hD hL f
    rw [actual_S4_eq_normalOrderedFourBodyForm] at h
    have hc : ((physicalSectorEquiv G theta ((M-4+2)+2)).symm f).val = p :=
      congrArg Subtype.val ((physicalSectorEquiv G theta ((M-4+2)+2)).symm_apply_apply ⟨p,hp'⟩)
    simpa only [physicalFourJetEnergy, hc, coreFourJetEnergy] using h

/-- The all-particle-number statement on the independently defined full
physical carrier, with the same S4 coefficient of its transported H square. -/
theorem fullCarrierFourJetEnergy_le_S4 (G : Geometry) (theta : Twist) (M D : ℕ)
    (hD : D ≤ 16) (hL : 20 ≤ systole G) (f : PhysicalBosonCarrier G theta M) :
    coreFourJetEnergy G theta D ((physicalSectorEquiv G theta M).symm f).val ≤
      (1+allowance) * (normalOrderedFourBodyForm G theta
        ((physicalSectorEquiv G theta M).symm f).val).re :=
  coreFourJetEnergy_le_S4 G theta M D hD hL _
    ((physicalSectorEquiv G theta M).symm f).property

#print axioms fullCarrierFourJetEnergy_le_S4
#print axioms fourBodyJet_low_sector
#print axioms coreFourJetEnergy_low_sector
#print axioms coreFourJetEnergy_le_S4
end TorusLean.Shared.BosonRelativeFrame
