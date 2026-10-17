import torus.shared.ThermalCoherentAllCoreBudget
import torus.shared.BosonThermalJacobiCutoff
import torus.shared.BosonThermalJacobiTail
import torus.shared.ThermalCoherentJacobiFourCutoff
import torus.shared.ThermalCoherentBosonRowIntegral

/-! Existing positive spectral cutoffs and the original row-metric payment
on every finite core. All original constants and source objects are unchanged;
the only new step is to use their previously proved all-core heat domains. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentAllCorePayments
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Boson.PhysicalContactLiftCandidate (contactCoreHamiltonian)
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4Coefficients
open TorusLean.Shared.ThermalCoherentAllCoreBudget
open TorusLean.Shared.BosonThermalJacobiCutoff TorusLean.Shared.BosonThermalJacobiTail
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.ThermalCoherentJacobiFourCutoff
open TorusLean.Shared.ThermalCoherentBosonRowEnvelope TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.LatticePacking
open scoped BigOperators
local instance allCorePayment_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem relative_cutoff_eight_allCore (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    (∑ d ∈ Finset.range 9, w3RelativeForm G theta d p) ≤ c3*sAllowance*
      (cAllowance*(normalOrderedFourBodyForm G theta p).re+
        (ip p (contactCoreHamiltonian G theta p)).re) := by
  have h := (relative_cutoff_weighted_bound G theta (1/12) (by norm_num) 8 p hG).trans
    (oneSpectatorForm_allCore_bound G theta (1/12) (by norm_num) p hG)
  norm_num [c3] at h ⊢
  nlinarith

theorem oddRelativeTail_allCore (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    (∑' d, oddRelativeTailTerm G theta p d) ≤ c9*sAllowance*
      (cAllowance*(normalOrderedFourBodyForm G theta p).re+
        (ip p (contactCoreHamiltonian G theta p)).re) := by
  have h := (oddRelativeTail_bound G theta p hG).2
  have he := oneSpectatorForm_allCore_bound G theta (2/27) (by norm_num) p hG
  have hh := mul_le_mul_of_nonneg_left he (show 0≤(20/9:ℝ)*(5/9:ℝ)^9 by positivity)
  refine h.trans (hh.trans_eq ?_)
  unfold c9
  ring

theorem auxiliaryEnvelope_allCore (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    (∫ R, auxiliaryEnvelope G theta 8 p R ∂cellMeasure G 2) ≤ (6*c3*sAllowance)*
      (cAllowance*(normalOrderedFourBodyForm G theta p).re+
        (ip p (contactCoreHamiltonian G theta p)).re) := by
  have h := mul_le_mul_of_nonneg_left (relative_cutoff_eight_allCore G theta p hG)
    (by norm_num : (0:ℝ)≤6)
  exact (auxiliaryEnvelope_eight_bound G theta p).trans (h.trans_eq (by ring))

theorem metric_allCore (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    |actualMetricForm G theta p| ≤ (kappaAllowance*c3*sAllowance)*
      (cAllowance*(normalOrderedFourBodyForm G theta p).re+
        (ip p (contactCoreHamiltonian G theta p)).re) := by
  have h := mul_le_mul_of_nonneg_left (auxiliaryEnvelope_allCore G theta p hG)
    (by norm_num [allowance,rowCost] : (0:ℝ)≤allowance*rowCost)
  apply (actualMetricForm_bound G theta p hG).trans
  convert h using 1 <;> dsimp [kappaAllowance] <;> ring

theorem four_relative_cutoff_sixteen_allCore (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (hG : 20≤systole G) :
    fourRelativeCutoffForm G theta 16 p ≤ c4*sAllowance^2*
      (2*cAllowance*(normalOrderedFourBodyForm G theta p).re+
        (ip p (contactCoreHamiltonian G theta p)).re) := by
  have h := (four_relative_cutoff_weighted_bound G theta (1/16) (by norm_num) 16 p hG).trans
    (twoSpectatorForm_allCore_bound G theta (1/16) (by norm_num) p hG)
  apply (mul_le_mul_iff_right₀
    (by norm_num : (0:ℝ)<(1/(1+1/16))*(1/(1+2*(1/16)))^(16+1))).mp
  calc
    _ ≤ _ := h
    _ = _ := by norm_num [c4] <;> ring

end TorusLean.Shared.ThermalCoherentAllCorePayments
