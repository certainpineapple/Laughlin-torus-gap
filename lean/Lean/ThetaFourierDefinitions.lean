import ThetaAnalyticBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

namespace TorusLean.Geometry.ThetaFourier

open Complex Real
open scoped Interval

/-- Fourier coefficients extracted by an actual integral of the section
along the real unit cycle, with the first-cycle twist removed. -/
def fourierExtract (sigma : ℂ) (F : ℂ → ℂ) (n : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    Complex.exp (-2 * π * I * ((n : ℂ) + sigma) * (t : ℂ)) * F (t : ℂ)

def untwist (sigma : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-2 * π * I * sigma * z) * F z

end TorusLean.Geometry.ThetaFourier
