import torus.shared.BosonNatThreeActualSourceTrace
import torus.shared.BosonNatThreeCOMReindex

/-! The complete original M3 source sum after genuine cell COM integration.
The relative coefficients are the old inverse-Gram weighted averages. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeActualCOMAverage
open TorusLean.Boson TorusLean.BosonFiniteCertificate TorusLean.M2 Matrix
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.BosonNatThreeCOMColumnTransport
open TorusLean.Shared.BosonNatThreeCOMCellTrace
open TorusLean.Shared.BosonNatThreeCellLift
open TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonNatThreeActualSourceTrace
open TorusLean.Shared.BosonNatThreeCOMReindex
open MeasureTheory
open scoped BigOperators

theorem natMatrixCellLiftForm_sum_cross (G : Geometry) (theta : Twist)
    (k : ℕ) {r : ℕ} (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixCellLiftForm G theta k p hp C f =
    (∑ i, ∑ j, C i j * (∫ R, ip
      (natThreeRemoval G theta (p i) (hp i) 0 R f)
      (natThreeRemoval G theta (p j) (hp j) 0 R f) ∂cellMeasure G k)).re := by
  rw [natMatrixCellLiftForm_eq_integral_re]
  simp_rw [natThreeAnnihilator_ground G theta _ (hp _)]
  have hi (i j : Fin r) := (natThreeRemoval_cross_integrable G theta k
    (p i) (p j) (hp i) (hp j) 0 0 f f).const_mul (C i j)
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j), integral_const_mul]

theorem original_M3_full_source_sum_eq_relative_average
    (G : Geometry) (theta : Twist) (f : Core (OrbitalIndex G theta) ℂ) :
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
      (complexify p308Ginv * k308actualM3 * complexify p308Ginv) f =
    natMatrixCellLiftForm G theta 3 (fun a : Fin 1 => natCOMRelativeColumn (⟨0,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩)
      (fun a => natCOMRelativeColumn_particle (⟨0,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) (complexify k300J * complexify c300averageRaw * complexify k300J) f +
    natMatrixCellLiftForm G theta 3 (fun a : Fin 0 => natCOMRelativeColumn (⟨1,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩)
      (fun a => natCOMRelativeColumn_particle (⟨1,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) (complexify k301J * complexify c301averageRaw * complexify k301J) f +
    natMatrixCellLiftForm G theta 3 (fun a : Fin 1 => natCOMRelativeColumn (⟨2,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩)
      (fun a => natCOMRelativeColumn_particle (⟨2,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) (complexify k302J * complexify c302averageRaw * complexify k302J) f +
    natMatrixCellLiftForm G theta 3 (fun a : Fin 1 => natCOMRelativeColumn (⟨3,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩)
      (fun a => natCOMRelativeColumn_particle (⟨3,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) (complexify k303J * complexify c303averageRaw * complexify k303J) f +
    natMatrixCellLiftForm G theta 3 (fun a : Fin 1 => natCOMRelativeColumn (⟨4,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩)
      (fun a => natCOMRelativeColumn_particle (⟨4,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) (complexify k304J * complexify c304averageRaw * complexify k304J) f +
    natMatrixCellLiftForm G theta 3 (fun a : Fin 1 => natCOMRelativeColumn (⟨5,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩)
      (fun a => natCOMRelativeColumn_particle (⟨5,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) (complexify k305J * complexify c305averageRaw * complexify k305J) f +
    natMatrixCellLiftForm G theta 3 (fun a : Fin 2 => natCOMRelativeColumn (⟨6,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩)
      (fun a => natCOMRelativeColumn_particle (⟨6,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) (complexify k306J * complexify c306averageRaw * complexify k306J) f +
    natMatrixCellLiftForm G theta 3 (fun a : Fin 1 => natCOMRelativeColumn (⟨7,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩)
      (fun a => natCOMRelativeColumn_particle (⟨7,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) (complexify k307J * complexify c307averageRaw * complexify k307J) f +
    natMatrixCellLiftForm G theta 3 (fun a : Fin 2 => natCOMRelativeColumn (⟨8,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩)
      (fun a => natCOMRelativeColumn_particle (⟨8,by decide⟩ : Fin 9) ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩) (complexify k308J * complexify c308averageRaw * complexify k308J) f := by
  let F : NatCOMRelativeLabel → NatCOMRelativeLabel → ℂ := fun u v =>
    ∫ R, ip (natThreeRemoval G theta (natCOMRelativeColumn u.1 u.2)
      (natCOMRelativeColumn_particle u.1 u.2) 0 R f)
      (natThreeRemoval G theta (natCOMRelativeColumn v.1 v.2)
      (natCOMRelativeColumn_particle v.1 v.2) 0 R f) ∂cellMeasure G 3
  have h := complete_COM_trace_regroup
    k300COMRankCoefficient k301COMRankCoefficient k302COMRankCoefficient k303COMRankCoefficient k304COMRankCoefficient k305COMRankCoefficient k306COMRankCoefficient k307COMRankCoefficient k308COMRankCoefficient
    (complexify k300J * complexify c300averageRaw * complexify k300J) (complexify k301J * complexify c301averageRaw * complexify k301J) (complexify k302J * complexify c302averageRaw * complexify k302J) (complexify k303J * complexify c303averageRaw * complexify k303J) (complexify k304J * complexify c304averageRaw * complexify k304J) (complexify k305J * complexify c305averageRaw * complexify k305J) (complexify k306J * complexify c306averageRaw * complexify k306J) (complexify k307J * complexify c307averageRaw * complexify k307J) (complexify k308J * complexify c308averageRaw * complexify k308J)
    F (by simpa only [c300_COM_reconstructed] using k300_COM_averaged_rank_entry) (by simpa only [c301_COM_reconstructed] using k301_COM_averaged_rank_entry) (by simpa only [c302_COM_reconstructed] using k302_COM_averaged_rank_entry) (by simpa only [c303_COM_reconstructed] using k303_COM_averaged_rank_entry) (by simpa only [c304_COM_reconstructed] using k304_COM_averaged_rank_entry) (by simpa only [c305_COM_reconstructed] using k305_COM_averaged_rank_entry) (by simpa only [c306_COM_reconstructed] using k306_COM_averaged_rank_entry) (by simpa only [c307_COM_reconstructed] using k307_COM_averaged_rank_entry) (by simpa only [c308_COM_reconstructed] using k308_COM_averaged_rank_entry) 
  rw [k300_original_source_L3_trace, k301_original_source_L3_trace, k302_original_source_L3_trace, k303_original_source_L3_trace, k304_original_source_L3_trace, k305_original_source_L3_trace, k306_original_source_L3_trace, k307_original_source_L3_trace, k308_original_source_L3_trace]
  simp_rw [natMatrixCellLiftForm_sum_cross]
  simpa only [F, Complex.add_re] using congrArg Complex.re h

end TorusLean.Shared.BosonNatThreeActualCOMAverage
