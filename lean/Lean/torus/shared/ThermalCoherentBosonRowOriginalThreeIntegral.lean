import torus.shared.ThermalCoherentBosonRowOriginalThree
import torus.shared.BosonNatThreeSourceEnergyComparison

/-! The actual raw K3 density integrates to the unchanged original M3 full-L3
source form. All cell domains are proved before the finite integral sums.
The previously established COM source change is reused with charge two. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowOriginalThree
open MeasureTheory TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Shared.BosonNatThreeCellLift TorusLean.Shared.BosonNatThreeActualCOMCellLift
open TorusLean.Shared.BosonNatThreeSourceEnergyComparison
open TorusLean.Shared.BosonFiniteCertificateCoordinate TorusLean.M2
open scoped BigOperators

/-- Complex integral of the genuine raw three-body term, identified with
exactly the original full-source L3 form already used by the certificate. -/
theorem actualRows_three_original_complex_integral (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ ρ : RowIndex, actualRowThreeCross G theta ρ R f f ∂cellMeasure G 2).re =
      originalM3SourceCellForm G theta f := by
  have h0 := natMatrixCellLiftForm_annihilator_integrable G theta 2
    k300COMDescendantFamily
    (actual_COM_family_particle k300occ k300_particle_degree (complexify k300COMBasis)
      k300COMDescendantFamily k300_COMDescendantFamily_column)
    k300COMRankCoefficient f f
  have h1 := natMatrixCellLiftForm_annihilator_integrable G theta 2
    k301COMDescendantFamily
    (actual_COM_family_particle k301occ k301_particle_degree (complexify k301COMBasis)
      k301COMDescendantFamily k301_COMDescendantFamily_column)
    k301COMRankCoefficient f f
  have h2 := natMatrixCellLiftForm_annihilator_integrable G theta 2
    k302COMDescendantFamily
    (actual_COM_family_particle k302occ k302_particle_degree (complexify k302COMBasis)
      k302COMDescendantFamily k302_COMDescendantFamily_column)
    k302COMRankCoefficient f f
  have h3 := natMatrixCellLiftForm_annihilator_integrable G theta 2
    k303COMDescendantFamily
    (actual_COM_family_particle k303occ k303_particle_degree (complexify k303COMBasis)
      k303COMDescendantFamily k303_COMDescendantFamily_column)
    k303COMRankCoefficient f f
  have h4 := natMatrixCellLiftForm_annihilator_integrable G theta 2
    k304COMDescendantFamily
    (actual_COM_family_particle k304occ k304_particle_degree (complexify k304COMBasis)
      k304COMDescendantFamily k304_COMDescendantFamily_column)
    k304COMRankCoefficient f f
  have h5 := natMatrixCellLiftForm_annihilator_integrable G theta 2
    k305COMDescendantFamily
    (actual_COM_family_particle k305occ k305_particle_degree (complexify k305COMBasis)
      k305COMDescendantFamily k305_COMDescendantFamily_column)
    k305COMRankCoefficient f f
  have h6 := natMatrixCellLiftForm_annihilator_integrable G theta 2
    k306COMDescendantFamily
    (actual_COM_family_particle k306occ k306_particle_degree (complexify k306COMBasis)
      k306COMDescendantFamily k306_COMDescendantFamily_column)
    k306COMRankCoefficient f f
  have h7 := natMatrixCellLiftForm_annihilator_integrable G theta 2
    k307COMDescendantFamily
    (actual_COM_family_particle k307occ k307_particle_degree (complexify k307COMBasis)
      k307COMDescendantFamily k307_COMDescendantFamily_column)
    k307COMRankCoefficient f f
  have h8 := natMatrixCellLiftForm_annihilator_integrable G theta 2
    k308COMDescendantFamily
    (actual_COM_family_particle k308occ k308_particle_degree (complexify k308COMBasis)
      k308COMDescendantFamily k308_COMDescendantFamily_column)
    k308COMRankCoefficient f f
  unfold originalM3SourceCellForm
  rw [←k300_actual_source_L3_COM,
    ←k301_actual_source_L3_COM,
    ←k302_actual_source_L3_COM,
    ←k303_actual_source_L3_COM,
    ←k304_actual_source_L3_COM,
    ←k305_actual_source_L3_COM,
    ←k306_actual_source_L3_COM,
    ←k307_actual_source_L3_COM,
    ←k308_actual_source_L3_COM]
  simp only [natMatrixCellLiftForm_eq_integral_re,←Complex.add_re]
  congr 1
  simp_rw [actualRows_three_original_cross,originalM3COMCross_eq_nine]
  have hsplit8 := integral_add (((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7) h8
  simp only [Pi.add_apply] at hsplit8
  rw [hsplit8]
  have hsplit7 := integral_add ((((((h0.add h1).add h2).add h3).add h4).add h5).add h6) h7
  simp only [Pi.add_apply] at hsplit7
  rw [hsplit7]
  have hsplit6 := integral_add (((((h0.add h1).add h2).add h3).add h4).add h5) h6
  simp only [Pi.add_apply] at hsplit6
  rw [hsplit6]
  have hsplit5 := integral_add ((((h0.add h1).add h2).add h3).add h4) h5
  simp only [Pi.add_apply] at hsplit5
  rw [hsplit5]
  have hsplit4 := integral_add (((h0.add h1).add h2).add h3) h4
  simp only [Pi.add_apply] at hsplit4
  rw [hsplit4]
  have hsplit3 := integral_add ((h0.add h1).add h2) h3
  simp only [Pi.add_apply] at hsplit3
  rw [hsplit3]
  have hsplit2 := integral_add (h0.add h1) h2
  simp only [Pi.add_apply] at hsplit2
  rw [hsplit2]
  have hsplit1 := integral_add h0 h1
  rw [hsplit1]

/-- Real-form endpoint in exactly the raw K normal-square decomposition. -/
theorem actualRows_three_original_integral (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, ∑ ρ : RowIndex, (actualRowThreeCross G theta ρ R f f).re ∂cellMeasure G 2) =
      originalM3SourceCellForm G theta f := by
  have h := integral_re (integrable_finsetSum Finset.univ
    (fun ρ _ => actualRowThreeCross_integrable G theta ρ f f))
  change (∫ R, (∑ ρ : RowIndex, actualRowThreeCross G theta ρ R f f).re ∂cellMeasure G 2) =
    (∫ R, ∑ ρ : RowIndex, actualRowThreeCross G theta ρ R f f ∂cellMeasure G 2).re at h
  simp only [Complex.re_sum] at h
  exact h.trans (actualRows_three_original_complex_integral G theta f)

end TorusLean.Shared.ThermalCoherentBosonRowOriginalThree
