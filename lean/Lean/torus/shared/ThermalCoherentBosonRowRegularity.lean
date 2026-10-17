import torus.shared.ThermalCoherentBosonRowSource
import torus.shared.ThermalCoherentRegularity

/-! Genuine cell domains for the original finite row square and its Gram
correction. Continuity follows from actual finite coefficient expansions,
without placing a topology or a bounded operator norm on the full Fock core. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open MeasureTheory TorusLean.Geometry TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.ThermalCoherentBosonRowCCR TorusLean.Shared.ThermalCoherentRegularity
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonThreeBodyLift TorusLean.Shared.BosonAnchoredNatLinearActions
open TorusLean.Shared.BosonNaturalWordSpan TorusLean.Shared.BosonNormalizedNatSeeds
open TorusLean.Shared.BosonAnchoredNatRaiseIntertwining
open TorusLean.Shared.ThermalCoherentSpectralOccupation TorusLean.Shared.PlaneJetParameterContinuity
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.RelativeJetMap
open scoped BigOperators ComplexConjugate
local instance rowRegular_nonempty (G : Geometry) (theta : Twist) : Nonempty (OrbitalIndex G theta) :=
  ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private theorem row_rawJet_coord_continuous (G : Geometry) (theta : Twist) (i : ℕ)
    (a : OrbitalIndex G theta) : Continuous (fun R => rawJetMode G theta i R a) := by
  simp only [rawJetMode,OrthonormalBasis.repr_apply_apply]
  exact continuous_const.inner (rawPlaneJet_continuous G theta i)

private theorem row_grouped_expansion (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (R : ℂ) (i : Fin 9) (f : Core (OrbitalIndex G theta) ℂ) :
    actualRowGrouped G theta ρ R i f =
      ∑ a, conj (seedDualMapNat G theta (tripleVacuum a).val (rowThreeAuxiliarySeed ρ i) R) •
        tripleRemove a f := by
  rw [actualRowGrouped_eq_source,natThreeAnnihilator_ground G theta _
    (rowThreeAuxiliarySeed_sector ρ i),natThreeRemoval_expansion]
  simp only [normalizedNatSeed_zero]

/-- Actual all-core row-square continuity from a finite coefficient family. -/
theorem actualRow_normSq_continuous (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (f : Core (OrbitalIndex G theta) ℂ) : Continuous (fun R => q (actualRow G theta ρ R f)) := by
  let J := Sum (TwoBodyLift.PairIndex (OrbitalIndex G theta))
    (Fin 9 × TripleIndex (OrbitalIndex G theta) × OrbitalIndex G theta)
  let c : J → ℂ → ℂ := Sum.elim
    (fun a R => (rowLambda ρ:ℂ)*chargeTwoJetEvaluation G theta ρ.1.val R (pairSection G theta a))
    (fun z R => conj (seedDualMapNat G theta (tripleVacuum z.2.1).val
      (rowThreeAuxiliarySeed ρ z.1) R)*rawJetMode G theta z.1.val R z.2.2)
  let v : J → Core (OrbitalIndex G theta) ℂ := Sum.elim
    (fun a => pairRemove a f) (fun z => create z.2.2 (tripleRemove z.2.1 f))
  have hc (z : J) : Continuous (c z) := by
    cases z with
    | inl a =>
      change Continuous (fun R : ℂ => (rowLambda ρ:ℂ)*
        chargeTwoJetEvaluation G theta ρ.1.val R (pairSection G theta a))
      exact continuous_const.mul
        (FermionLocalJet.chargeTwoJetEvaluation_continuous G theta (pairSection G theta a) _)
    | inr z =>
      change Continuous (fun R : ℂ => conj (seedDualMapNat G theta (tripleVacuum z.2.1).val
        (rowThreeAuxiliarySeed ρ z.1) R)*rawJetMode G theta z.1.val R z.2.2)
      exact
        ((seedDualNat_contDiff G theta 3 (tripleVacuum z.2.1).val _
          (homogeneous_mem_naturalWordSpan 3 _ (rowThreeAuxiliarySeed_sector ρ z.1))).continuous.star).mul
        (row_rawJet_coord_continuous G theta _ _)
  have he (R : ℂ) : actualRow G theta ρ R f=∑ z : J, c z R • v z := by
    rw [actualRow_eq_grouped]
    simp only [rowApply,actualRowPair,pairDescendant,LinearMap.smul_apply,LinearMap.sum_apply,
      row_grouped_expansion,map_sum,map_smul,modeCreate,LinearMap.sum_apply,LinearMap.smul_apply,
      Finset.smul_sum,smul_smul,Fintype.sum_sum_type,Fintype.sum_prod_type,J,c,v,Sum.elim_inl,Sum.elim_inr]
  simp_rw [he]
  exact finite_combination_normSq_continuous c hc v

/-- The positive original row form has an honest cell integral. -/
theorem actualRow_normSq_integrable (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => q (actualRow G theta ρ R f)) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2 (actualRow_normSq_continuous G theta ρ f)

private theorem source_cross_continuous (G : Geometry) (theta : Twist) (p r : Core ℕ ℂ)
    (hp : p.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    Continuous (fun R => ip (natThreeAnnihilator G theta R p f)
      (natThreeAnnihilator G theta R r g)) := by
  simp_rw [natThreeAnnihilator_ground G theta p hp,natThreeAnnihilator_ground G theta r hr,
    natThreeRemoval_cross_expansion,normalizedNatSeed_zero]
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  exact continuous_const.mul
    (((seedDualNat_contDiff G theta 3 (tripleVacuum b).val _
      (homogeneous_mem_naturalWordSpan 3 r hr)).continuous.star).mul
      (seedDualNat_contDiff G theta 3 (tripleVacuum a).val _
        (homogeneous_mem_naturalWordSpan 3 p hp)).continuous)

/-- Raw Gram correction is continuous with the exact off-diagonal overlaps. -/
theorem actualRowMetricCross_continuous (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    Continuous (fun R => actualRowMetricCross G theta ρ R f g) := by
  simp only [actualRowMetricCross,rowMetricCross,rawJetMode,LinearIsometryEquiv.inner_map_map]
  simp_rw [actualRowGrouped_eq_source]
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  exact (((rawPlaneJet_continuous G theta i.val).inner
    (rawPlaneJet_continuous G theta j.val)).sub continuous_const).mul
    (source_cross_continuous G theta _ _
      (rowThreeAuxiliarySeed_sector ρ i) (rowThreeAuxiliarySeed_sector ρ j) f g)

theorem actualRowMetricCross_integrable (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => actualRowMetricCross G theta ρ R f g) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2 (actualRowMetricCross_continuous G theta ρ f g)

end TorusLean.Shared.ThermalCoherentBosonRows
