import torus.shared.BosonNatFourOriginalMatrixBound
import torus.shared.BosonNatFourRelativeMatrixImages
import torus.shared.BosonNatFourRelativeSourceBudget
import torus.shared.ThermalCoherentAllCorePayments

/-! The unchanged original M4 source is paid by the same physical normal-S4
and contact-H forms, after the complete original N4 COM certificate transport. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourOriginalPhysicalPayment
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Boson.PhysicalContactLiftCandidate (contactCoreHamiltonian)
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4Coefficients
open TorusLean.Shared.ThermalCoherentBosonRowOriginalFourLift
open TorusLean.Shared.BosonNatFourOriginalMatrixBound
open TorusLean.Shared.BosonNatFourRelativeMatrixImages
open TorusLean.Shared.BosonNatFourRelativeSourceBudget
open TorusLean.Shared.ThermalCoherentAllCorePayments
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.LatticePacking
open scoped BigOperators
local instance originalPayment_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem originalM4SourceCellForm_allM_bound (G : Geometry) (theta : Twist)
    (M : ℕ) (f : Core (OrbitalIndex G theta) ℂ) (hf : f.IsHomogeneous M)
    (hG : 20≤systole G) :
    originalM4SourceCellForm G theta f ≤
      alpha*sAllowance*(normalOrderedFourBodyForm G theta f).re +
      delta*c4*sAllowance^2*(2*cAllowance*(normalOrderedFourBodyForm G theta f).re+
        (ip f (contactCoreHamiltonian G theta f)).re) := by
  have h := originalM4SourceCellForm_relative_matrix_bound G theta f
  simp_rw [natFourRelativeS4MatrixCell_eq_source] at h
  rw [natFourRelativeHMatrixCell_sum_eq_cutoff] at h
  have ha : (TorusLean.BosonFiniteCertificate.alpha : ℝ)=alpha := by
    norm_num [TorusLean.BosonFiniteCertificate.alpha,alpha,c9]
  have hd : (TorusLean.BosonFiniteCertificate.delta : ℝ)=delta := by
    norm_num [TorusLean.BosonFiniteCertificate.delta,delta]
  rw [ha,hd] at h
  have hS := w4RelativeForm_s4_cutoff_allM_bound G theta M 16 (by omega) hG f hf
  have hH := four_relative_cutoff_sixteen_allCore G theta f hG
  have ha0 : 0≤alpha := by norm_num [alpha,c9]
  have hd0 : 0≤delta := by norm_num [delta]
  calc
    _ ≤ _ := h
    _ ≤ alpha*(sAllowance*(normalOrderedFourBodyForm G theta f).re) +
        delta*(c4*sAllowance^2*(2*cAllowance*(normalOrderedFourBodyForm G theta f).re+
          (ip f (contactCoreHamiltonian G theta f)).re)) :=
      add_le_add (mul_le_mul_of_nonneg_left hS ha0) (mul_le_mul_of_nonneg_left hH hd0)
    _ = _ := by ring

#print axioms originalM4SourceCellForm_allM_bound
end TorusLean.Shared.BosonNatFourOriginalPhysicalPayment
