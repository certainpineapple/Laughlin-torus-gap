import torus.shared.BosonNatFourOriginalRelativeAverage
import torus.shared.BosonNatFourMatrixComparison

/-! The original seventeen comparison certificates are applied to the actual
full-L4 cell forms after their true complete COM trace. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourOriginalMatrixBound
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.BosonNatFourMatrixComparison
open TorusLean.Shared.BosonNatFourOriginalRelativeAverage
open TorusLean.Shared.ThermalCoherentBosonRowOriginalFourLift
open scoped BigOperators ComplexOrder

/-- The actual original source-cell form satisfies the full original
seventeen-block comparison, with both inverse Gram factors retained. -/
theorem originalM4SourceCellForm_relative_matrix_bound (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    originalM4SourceCellForm G theta f ≤
      (alpha : ℝ) * (∑ d : Fin 17, natFourMatrixCellLiftForm G theta 4
        (natFourRelativeColumn d) (fun a => (natFourRelativeColumn_bihomogeneous d a).1)
        (natFourRelativeS4RankCoefficient d) f) +
      (delta : ℝ) * (∑ d : Fin 17, natFourMatrixCellLiftForm G theta 4
        (natFourRelativeColumn d) (fun a => (natFourRelativeColumn_bihomogeneous d a).1)
        (natFourRelativeHRankCoefficient d) f) := by
  rw [originalM4SourceCellForm_eq_relative_matrices]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  apply natFourMatrixCellLiftForm_compare
  have h := natFourRelativeComparisonRankCoefficient_posSemidef d
  rw [natFourRelativeComparisonRankCoefficient_eq] at h
  convert h using 1; push_cast; abel

#print axioms originalM4SourceCellForm_relative_matrix_bound
end TorusLean.Shared.BosonNatFourOriginalMatrixBound
