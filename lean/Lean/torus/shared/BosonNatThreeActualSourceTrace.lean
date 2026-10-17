import torus.shared.BosonNatThreeCOMCellTrace
import torus.shared.BosonNatThreeActualCOMCellLift

/-! The original M3 full-source rank densities through the actual charge-two
full L3 integral, evaluated by the genuine unnormalized COM cell trace. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeActualSourceTrace
open TorusLean.Boson TorusLean.BosonFiniteCertificate TorusLean.M2
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeCOMColumnTransport
open TorusLean.Shared.BosonNatThreeCOMCellTrace
open TorusLean.Shared.BosonNatThreeActualCOMCellLift
open TorusLean.Shared.BosonNatThreeCellLift
open TorusLean.Shared.BosonNatThreeRemovalTrace
open MeasureTheory
open scoped BigOperators

theorem k300_original_source_L3_trace (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k300occ)
      (natOccupationColumns_particle k300occ k300_particle_degree)
      (complexify p300Ginv * k300actualM3 * complexify p300Ginv) f =
    ((2/3:ℂ) * ∑ i, ∑ j, if k300COMLevel i=k300COMLevel j then
      (3^(k300COMLevel i)*((k300COMLevel i).factorial:ℂ))*k300COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k300COMRelativeDegree i) (k300COMIndexLabel i).2) (natCOMRelativeColumn_particle (k300COMRelativeDegree i) (k300COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k300COMRelativeDegree j) (k300COMIndexLabel j).2) (natCOMRelativeColumn_particle (k300COMRelativeDegree j) (k300COMIndexLabel j).2) 0 R f) ∂cellMeasure G 3)
      else 0).re := by
  rw [← k300_actual_source_L3_COM,natMatrixCellLiftForm_eq_integral_re,
    k300_actual_COM_cell_trace]

theorem k301_original_source_L3_trace (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k301occ)
      (natOccupationColumns_particle k301occ k301_particle_degree)
      (complexify p301Ginv * k301actualM3 * complexify p301Ginv) f =
    ((2/3:ℂ) * ∑ i, ∑ j, if k301COMLevel i=k301COMLevel j then
      (3^(k301COMLevel i)*((k301COMLevel i).factorial:ℂ))*k301COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k301COMRelativeDegree i) (k301COMIndexLabel i).2) (natCOMRelativeColumn_particle (k301COMRelativeDegree i) (k301COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k301COMRelativeDegree j) (k301COMIndexLabel j).2) (natCOMRelativeColumn_particle (k301COMRelativeDegree j) (k301COMIndexLabel j).2) 0 R f) ∂cellMeasure G 3)
      else 0).re := by
  rw [← k301_actual_source_L3_COM,natMatrixCellLiftForm_eq_integral_re,
    k301_actual_COM_cell_trace]

theorem k302_original_source_L3_trace (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k302occ)
      (natOccupationColumns_particle k302occ k302_particle_degree)
      (complexify p302Ginv * k302actualM3 * complexify p302Ginv) f =
    ((2/3:ℂ) * ∑ i, ∑ j, if k302COMLevel i=k302COMLevel j then
      (3^(k302COMLevel i)*((k302COMLevel i).factorial:ℂ))*k302COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k302COMRelativeDegree i) (k302COMIndexLabel i).2) (natCOMRelativeColumn_particle (k302COMRelativeDegree i) (k302COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k302COMRelativeDegree j) (k302COMIndexLabel j).2) (natCOMRelativeColumn_particle (k302COMRelativeDegree j) (k302COMIndexLabel j).2) 0 R f) ∂cellMeasure G 3)
      else 0).re := by
  rw [← k302_actual_source_L3_COM,natMatrixCellLiftForm_eq_integral_re,
    k302_actual_COM_cell_trace]

theorem k303_original_source_L3_trace (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k303occ)
      (natOccupationColumns_particle k303occ k303_particle_degree)
      (complexify p303Ginv * k303actualM3 * complexify p303Ginv) f =
    ((2/3:ℂ) * ∑ i, ∑ j, if k303COMLevel i=k303COMLevel j then
      (3^(k303COMLevel i)*((k303COMLevel i).factorial:ℂ))*k303COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k303COMRelativeDegree i) (k303COMIndexLabel i).2) (natCOMRelativeColumn_particle (k303COMRelativeDegree i) (k303COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k303COMRelativeDegree j) (k303COMIndexLabel j).2) (natCOMRelativeColumn_particle (k303COMRelativeDegree j) (k303COMIndexLabel j).2) 0 R f) ∂cellMeasure G 3)
      else 0).re := by
  rw [← k303_actual_source_L3_COM,natMatrixCellLiftForm_eq_integral_re,
    k303_actual_COM_cell_trace]

theorem k304_original_source_L3_trace (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k304occ)
      (natOccupationColumns_particle k304occ k304_particle_degree)
      (complexify p304Ginv * k304actualM3 * complexify p304Ginv) f =
    ((2/3:ℂ) * ∑ i, ∑ j, if k304COMLevel i=k304COMLevel j then
      (3^(k304COMLevel i)*((k304COMLevel i).factorial:ℂ))*k304COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k304COMRelativeDegree i) (k304COMIndexLabel i).2) (natCOMRelativeColumn_particle (k304COMRelativeDegree i) (k304COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k304COMRelativeDegree j) (k304COMIndexLabel j).2) (natCOMRelativeColumn_particle (k304COMRelativeDegree j) (k304COMIndexLabel j).2) 0 R f) ∂cellMeasure G 3)
      else 0).re := by
  rw [← k304_actual_source_L3_COM,natMatrixCellLiftForm_eq_integral_re,
    k304_actual_COM_cell_trace]

theorem k305_original_source_L3_trace (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k305occ)
      (natOccupationColumns_particle k305occ k305_particle_degree)
      (complexify p305Ginv * k305actualM3 * complexify p305Ginv) f =
    ((2/3:ℂ) * ∑ i, ∑ j, if k305COMLevel i=k305COMLevel j then
      (3^(k305COMLevel i)*((k305COMLevel i).factorial:ℂ))*k305COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k305COMRelativeDegree i) (k305COMIndexLabel i).2) (natCOMRelativeColumn_particle (k305COMRelativeDegree i) (k305COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k305COMRelativeDegree j) (k305COMIndexLabel j).2) (natCOMRelativeColumn_particle (k305COMRelativeDegree j) (k305COMIndexLabel j).2) 0 R f) ∂cellMeasure G 3)
      else 0).re := by
  rw [← k305_actual_source_L3_COM,natMatrixCellLiftForm_eq_integral_re,
    k305_actual_COM_cell_trace]

theorem k306_original_source_L3_trace (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k306occ)
      (natOccupationColumns_particle k306occ k306_particle_degree)
      (complexify p306Ginv * k306actualM3 * complexify p306Ginv) f =
    ((2/3:ℂ) * ∑ i, ∑ j, if k306COMLevel i=k306COMLevel j then
      (3^(k306COMLevel i)*((k306COMLevel i).factorial:ℂ))*k306COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k306COMRelativeDegree i) (k306COMIndexLabel i).2) (natCOMRelativeColumn_particle (k306COMRelativeDegree i) (k306COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k306COMRelativeDegree j) (k306COMIndexLabel j).2) (natCOMRelativeColumn_particle (k306COMRelativeDegree j) (k306COMIndexLabel j).2) 0 R f) ∂cellMeasure G 3)
      else 0).re := by
  rw [← k306_actual_source_L3_COM,natMatrixCellLiftForm_eq_integral_re,
    k306_actual_COM_cell_trace]

theorem k307_original_source_L3_trace (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k307occ)
      (natOccupationColumns_particle k307occ k307_particle_degree)
      (complexify p307Ginv * k307actualM3 * complexify p307Ginv) f =
    ((2/3:ℂ) * ∑ i, ∑ j, if k307COMLevel i=k307COMLevel j then
      (3^(k307COMLevel i)*((k307COMLevel i).factorial:ℂ))*k307COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k307COMRelativeDegree i) (k307COMIndexLabel i).2) (natCOMRelativeColumn_particle (k307COMRelativeDegree i) (k307COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k307COMRelativeDegree j) (k307COMIndexLabel j).2) (natCOMRelativeColumn_particle (k307COMRelativeDegree j) (k307COMIndexLabel j).2) 0 R f) ∂cellMeasure G 3)
      else 0).re := by
  rw [← k307_actual_source_L3_COM,natMatrixCellLiftForm_eq_integral_re,
    k307_actual_COM_cell_trace]

theorem k308_original_source_L3_trace (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta 2 (natOccupationColumns k308occ)
      (natOccupationColumns_particle k308occ k308_particle_degree)
      (complexify p308Ginv * k308actualM3 * complexify p308Ginv) f =
    ((2/3:ℂ) * ∑ i, ∑ j, if k308COMLevel i=k308COMLevel j then
      (3^(k308COMLevel i)*((k308COMLevel i).factorial:ℂ))*k308COMRankCoefficient i j *
      (∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn (k308COMRelativeDegree i) (k308COMIndexLabel i).2) (natCOMRelativeColumn_particle (k308COMRelativeDegree i) (k308COMIndexLabel i).2) 0 R f)
        (natThreeRemoval G theta (natCOMRelativeColumn (k308COMRelativeDegree j) (k308COMIndexLabel j).2) (natCOMRelativeColumn_particle (k308COMRelativeDegree j) (k308COMIndexLabel j).2) 0 R f) ∂cellMeasure G 3)
      else 0).re := by
  rw [← k308_actual_source_L3_COM,natMatrixCellLiftForm_eq_integral_re,
    k308_actual_COM_cell_trace]

end TorusLean.Shared.BosonNatThreeActualSourceTrace
