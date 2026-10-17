import torus.shared.ThermalCoherentGaussian
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual Gaussian mass on the whole two-offset plane. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentDoubleGaussian
open MeasureTheory TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Shared.ThermalCoherentGaussian

local instance : SFinite planeMeasure := by
  unfold planeMeasure
  infer_instance

def thermalProductWeight (a : ℝ) (x : ℂ × ℂ) : ℝ :=
  thermalWeight a x.1 * thermalWeight a x.2

theorem thermalProductWeight_eq_exp (a : ℝ) (x : ℂ × ℂ) :
    thermalProductWeight a x = Real.exp (-a * (‖x.1‖^2 + ‖x.2‖^2)) := by
  rw [thermalProductWeight, thermalWeight, thermalWeight, ← Real.exp_add]
  congr 1
  ring

theorem thermalProductWeight_pos (a : ℝ) (x : ℂ × ℂ) :
    0 < thermalProductWeight a x := mul_pos (thermalWeight_pos a _) (thermalWeight_pos a _)

theorem thermalProductWeight_continuous (a : ℝ) : Continuous (thermalProductWeight a) :=
  ((thermalWeight_continuous a).comp continuous_fst).mul
    ((thermalWeight_continuous a).comp continuous_snd)

theorem thermalProductWeight_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (thermalProductWeight a) (planeMeasure.prod planeMeasure) :=
  (thermalWeight_integrable a ha).mul_prod (thermalWeight_integrable a ha)

theorem thermalProductWeight_integral (a : ℝ) (ha : 0 < a) :
    (∫ x, thermalProductWeight a x ∂planeMeasure.prod planeMeasure) = 1/a^2 := by
  unfold thermalProductWeight
  rw [integral_prod_mul, thermalWeight_integral a ha]
  ring

#print axioms thermalProductWeight_eq_exp
#print axioms thermalProductWeight_integrable
#print axioms thermalProductWeight_integral
end TorusLean.Shared.ThermalCoherentDoubleGaussian
