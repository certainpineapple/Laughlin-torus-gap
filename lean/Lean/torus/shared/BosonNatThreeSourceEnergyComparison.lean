import torus.shared.BosonNatThreeActualCOMAverage
import torus.shared.BosonNatThreeRelativeColumnIdentity
import torus.shared.BosonNatThreeCertifiedEnergyIdentity

/-! Actual original finite M3 source density compared through the unchanged
positive certificate with the true low-relative energy dyads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeSourceEnergyComparison
open TorusLean.Boson TorusLean.BosonFiniteCertificate TorusLean.M2 Matrix
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonNatThreeCOMColumnTransport
open TorusLean.Shared.BosonNatThreeCellLift
open TorusLean.Shared.BosonNatThreeActualCOMAverage
open TorusLean.Shared.BosonNatThreeRelativeColumnIdentity
open TorusLean.Shared.BosonNatThreeCertifiedEnergyIdentity
open TorusLean.Shared.BosonNatThreeCertifiedLift
open TorusLean.Shared.BosonThermalJacobiRows
open scoped BigOperators

def originalM3SourceCellForm (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k300occ)
      (natOccupationColumns_particle k300occ k300_particle_degree)
      (complexify p300Ginv * k300actualM3 * complexify p300Ginv) f +
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k301occ)
      (natOccupationColumns_particle k301occ k301_particle_degree)
      (complexify p301Ginv * k301actualM3 * complexify p301Ginv) f +
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k302occ)
      (natOccupationColumns_particle k302occ k302_particle_degree)
      (complexify p302Ginv * k302actualM3 * complexify p302Ginv) f +
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k303occ)
      (natOccupationColumns_particle k303occ k303_particle_degree)
      (complexify p303Ginv * k303actualM3 * complexify p303Ginv) f +
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k304occ)
      (natOccupationColumns_particle k304occ k304_particle_degree)
      (complexify p304Ginv * k304actualM3 * complexify p304Ginv) f +
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k305occ)
      (natOccupationColumns_particle k305occ k305_particle_degree)
      (complexify p305Ginv * k305actualM3 * complexify p305Ginv) f +
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k306occ)
      (natOccupationColumns_particle k306occ k306_particle_degree)
      (complexify p306Ginv * k306actualM3 * complexify p306Ginv) f +
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k307occ)
      (natOccupationColumns_particle k307occ k307_particle_degree)
      (complexify p307Ginv * k307actualM3 * complexify p307Ginv) f +
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k308occ)
      (natOccupationColumns_particle k308occ k308_particle_degree)
      (complexify p308Ginv * k308actualM3 * complexify p308Ginv) f

def lowRelativeEnergyForm (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∑ d ∈ Finset.range 9, (2*(-1/2:ℝ)^d+(delta:ℝ))*w3RelativeForm G theta d f

theorem originalM3SourceCellForm_eq_relative_average (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    originalM3SourceCellForm G theta f =
    natMatrixCellLiftForm G theta 3 k300natRelativeFamily
      (natFamilyOfFin9_particle k300family)
      (complexify k300J * complexify c300averageRaw * complexify k300J) f +
    natMatrixCellLiftForm G theta 3 k301natRelativeFamily
      (natFamilyOfFin9_particle k301family)
      (complexify k301J * complexify c301averageRaw * complexify k301J) f +
    natMatrixCellLiftForm G theta 3 k302natRelativeFamily
      (natFamilyOfFin9_particle k302family)
      (complexify k302J * complexify c302averageRaw * complexify k302J) f +
    natMatrixCellLiftForm G theta 3 k303natRelativeFamily
      (natFamilyOfFin9_particle k303family)
      (complexify k303J * complexify c303averageRaw * complexify k303J) f +
    natMatrixCellLiftForm G theta 3 k304natRelativeFamily
      (natFamilyOfFin9_particle k304family)
      (complexify k304J * complexify c304averageRaw * complexify k304J) f +
    natMatrixCellLiftForm G theta 3 k305natRelativeFamily
      (natFamilyOfFin9_particle k305family)
      (complexify k305J * complexify c305averageRaw * complexify k305J) f +
    natMatrixCellLiftForm G theta 3 k306natRelativeFamily
      (natFamilyOfFin9_particle k306family)
      (complexify k306J * complexify c306averageRaw * complexify k306J) f +
    natMatrixCellLiftForm G theta 3 k307natRelativeFamily
      (natFamilyOfFin9_particle k307family)
      (complexify k307J * complexify c307averageRaw * complexify k307J) f +
    natMatrixCellLiftForm G theta 3 k308natRelativeFamily
      (natFamilyOfFin9_particle k308family)
      (complexify k308J * complexify c308averageRaw * complexify k308J) f := by
  simpa only [originalM3SourceCellForm,k300_relativeColumn_eq_family,k301_relativeColumn_eq_family,k302_relativeColumn_eq_family,k303_relativeColumn_eq_family,k304_relativeColumn_eq_family,k305_relativeColumn_eq_family,k306_relativeColumn_eq_family,k307_relativeColumn_eq_family,k308_relativeColumn_eq_family] using
    original_M3_full_source_sum_eq_relative_average G theta f

theorem certifiedComparisonLift_energy_identity (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    certifiedComparisonLift G theta f =
      lowRelativeEnergyForm G theta f - originalM3SourceCellForm G theta f := by
  rw [certifiedComparisonLift,k300_certifiedLift_energy_difference,k301_certifiedLift_energy_difference,k302_certifiedLift_energy_difference,k303_certifiedLift_energy_difference,k304_certifiedLift_energy_difference,k305_certifiedLift_energy_difference,k306_certifiedLift_energy_difference,k307_certifiedLift_energy_difference,k308_certifiedLift_energy_difference,
    originalM3SourceCellForm_eq_relative_average]
  simp only [lowRelativeEnergyForm,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  ring

theorem originalM3SourceCellForm_le_low_energy (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    originalM3SourceCellForm G theta f ≤ lowRelativeEnergyForm G theta f := by
  have h := certifiedComparisonLift_nonneg G theta f
  rw [certifiedComparisonLift_energy_identity] at h
  linarith

end TorusLean.Shared.BosonNatThreeSourceEnergyComparison
