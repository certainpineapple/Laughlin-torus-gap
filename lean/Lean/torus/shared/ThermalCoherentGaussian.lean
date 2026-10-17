import CanonicalPlaneJets

/-! The actual full-plane Gaussian mass for thermal coherent offsets.
All offsets use d²β/π, without any cell truncation. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentGaussian
open MeasureTheory TorusLean.Fermion.PlaneMagneticUnitary

/-- Scalar thermal weight on the full complex plane. -/
def thermalWeight (a : ℝ) (β : ℂ) : ℝ := Real.exp (-a * ‖β‖^2)

theorem thermalWeight_pos (a : ℝ) (β : ℂ) : 0 < thermalWeight a β := Real.exp_pos _

theorem thermalWeight_continuous (a : ℝ) : Continuous (thermalWeight a) := by
  unfold thermalWeight
  fun_prop

theorem thermalWeight_volume_integral (a : ℝ) (ha : 0 < a) :
    (∫ β : ℂ, thermalWeight a β) = Real.pi / a := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := 0) (b := a) (by norm_num) (by norm_num) ha
  norm_num [Real.rpow_two, Real.rpow_neg_one, Real.Gamma_one] at h
  simpa only [thermalWeight, div_eq_mul_inv, neg_mul] using h

/-- Integrability is derived from the proved nonzero Gaussian integral. -/
theorem thermalWeight_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (thermalWeight a) planeMeasure := by
  have hv : Integrable (thermalWeight a) volume := by
    apply Integrable.of_integral_ne_zero
    rw [thermalWeight_volume_integral a ha]
    exact ne_of_gt (div_pos Real.pi_pos ha)
  exact hv.smul_measure (c := ENNReal.ofReal (1 / Real.pi)) (by simp)

theorem thermalWeight_integral (a : ℝ) (ha : 0 < a) :
    (∫ β, thermalWeight a β ∂planeMeasure) = 1 / a := by
  rw [planeMeasure, integral_smul_measure, thermalWeight_volume_integral a ha,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / Real.pi)]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

#print axioms thermalWeight_integrable
#print axioms thermalWeight_integral
end TorusLean.Shared.ThermalCoherentGaussian
