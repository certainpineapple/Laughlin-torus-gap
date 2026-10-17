import ThetaFourierDefinitions
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

noncomputable section

namespace TorusLean.Geometry.ThetaFourier

open Complex Real
open scoped Interval

/-- A holomorphic, one-periodic function has the same integral along every
horizontal unit segment. This is proved from a global complex primitive. -/
theorem integral_unit_translate (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hperiod : ∀ z : ℂ, g (z + 1) = g z) (z : ℂ) :
    (∫ t in (0 : ℝ)..1, g ((t : ℂ) + z)) =
      ∫ t in (0 : ℝ)..1, g (t : ℂ) := by
  obtain ⟨H, hH⟩ := hg.isExactOn_univ
  have hH' (w : ℂ) : HasDerivAt H (g w) w := hH w (Set.mem_univ w)
  have hD (w : ℂ) : HasDerivAt (fun w : ℂ => H (w + 1) - H w) 0 w := by
    have h := ((hH' (w + 1)).comp w ((hasDerivAt_id w).add_const 1)).sub (hH' w)
    simpa only [Function.comp_def, id_eq, Pi.sub_apply, mul_one, hperiod, sub_self] using! h
  have hconst := is_const_of_deriv_eq_zero (fun w => (hD w).differentiableAt)
    (fun w => (hD w).deriv) z 0
  have hFTC (w : ℂ) :
      (∫ t in (0 : ℝ)..1, g ((t : ℂ) + w)) = H (w + 1) - H w := by
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => H ((t : ℂ) + w))
        (g ((t : ℂ) + w)) t := by
      have h := (hH' ((t : ℂ) + w)).comp (t : ℂ)
        ((hasDerivAt_id (t : ℂ)).add_const w)
      simpa only [Function.comp_def, id_eq, mul_one] using! h.comp_ofReal
    have hc : Continuous (fun t : ℝ => g ((t : ℂ) + w)) :=
      hg.continuous.comp (Complex.continuous_ofReal.add continuous_const)
    simpa only [Complex.ofReal_one, Complex.ofReal_zero, zero_add, add_comm 1 w]
      using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        (hc.intervalIntegrable 0 1)
  rw [hFTC z]
  simpa only [add_zero, zero_add] using hconst.trans (hFTC 0).symm

/-- The entire integrand used to extract a twisted Fourier coefficient. -/
def fourierIntegrand (sigma : ℂ) (F : ℂ → ℂ) (n : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (-2 * π * I * ((n : ℂ) + sigma) * z) * F z

theorem fourierIntegrand_differentiable (sigma : ℂ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F) (n : ℤ) :
    Differentiable ℂ (fourierIntegrand sigma F n) := by
  exact (differentiable_id.const_mul _).cexp.mul hF

theorem fourierIntegrand_periodic (sigma : ℂ) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, F (z + 1) = Complex.exp (2 * π * I * sigma) * F z)
    (n : ℤ) (z : ℂ) :
    fourierIntegrand sigma F n (z + 1) = fourierIntegrand sigma F n z := by
  unfold fourierIntegrand
  rw [hF, ← mul_assoc, ← Complex.exp_add]
  have he : -2 * (π : ℂ) * I * ((n : ℂ) + sigma) * (z + 1) +
      2 * π * I * sigma =
      -2 * π * I * ((n : ℂ) + sigma) * z + ((-n : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The integral defining a coefficient can be taken on any translated unit
segment, because its full integrand is holomorphic and one-periodic. -/
theorem fourierExtract_translate (sigma : ℂ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hperiod : ∀ z : ℂ, F (z + 1) = Complex.exp (2 * π * I * sigma) * F z)
    (n : ℤ) (z : ℂ) :
    (∫ t in (0 : ℝ)..1, fourierIntegrand sigma F n ((t : ℂ) + z)) =
      fourierExtract sigma F n := by
  exact integral_unit_translate (fourierIntegrand sigma F n)
    (fourierIntegrand_differentiable sigma F hF n)
    (fourierIntegrand_periodic sigma F hperiod n) z

theorem fourierIntegrand_translate_tau (sigma psi tau : ℂ) (d : ℕ)
    (F : ℂ → ℂ)
    (htau : ∀ z : ℂ, F (z + tau) =
      Complex.exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z)
    (n : ℤ) (z : ℂ) :
    fourierIntegrand sigma F n (z + tau) =
      Complex.exp (-π * I * tau * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + I * psi) *
        fourierIntegrand sigma F (n + (d : ℤ)) z := by
  unfold fourierIntegrand
  rw [htau, ← mul_assoc, ← Complex.exp_add]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- The recurrence is obtained from the actual coefficient integral and the
two transformation laws of an arbitrary entire section. -/
theorem fourierExtract_recurrence (sigma psi tau : ℂ) (d : ℕ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hperiod : ∀ z : ℂ, F (z + 1) = Complex.exp (2 * π * I * sigma) * F z)
    (htau : ∀ z : ℂ, F (z + tau) =
      Complex.exp (I * psi - π * I * (d : ℂ) * (2 * z + tau)) * F z)
    (n : ℤ) :
    fourierExtract sigma F (n + (d : ℤ)) =
      Complex.exp (π * I * tau * (2 * ((n : ℂ) + sigma) + (d : ℂ)) - I * psi) *
        fourierExtract sigma F n := by
  have htranslate := fourierExtract_translate sigma F hF hperiod n tau
  have heval : fourierExtract sigma F n =
      Complex.exp (-π * I * tau * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + I * psi) *
        fourierExtract sigma F (n + (d : ℤ)) := by
    rw [← htranslate]
    simp only [fourierIntegrand_translate_tau sigma psi tau d F htau n,
      intervalIntegral.integral_const_mul]
    rfl
  calc
    fourierExtract sigma F (n + (d : ℤ)) =
        Complex.exp (π * I * tau * (2 * ((n : ℂ) + sigma) + (d : ℂ)) - I * psi) *
          (Complex.exp (-π * I * tau * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + I * psi) *
            fourierExtract sigma F (n + (d : ℤ))) := by
      rw [← mul_assoc, ← Complex.exp_add]
      have hz : (π * I * tau * (2 * ((n : ℂ) + sigma) + (d : ℂ)) - I * psi) +
          (-π * I * tau * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + I * psi) = 0 := by ring
      rw [hz, Complex.exp_zero, one_mul]
    _ = _ := by rw [← heval]

end TorusLean.Geometry.ThetaFourier
