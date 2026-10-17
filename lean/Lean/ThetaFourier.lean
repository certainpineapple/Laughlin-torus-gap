import ThetaFourierDefinitions
import ThetaFourierSeries

set_option autoImplicit false

/-!
Actual integral Fourier extraction of the already constructed entire sections.
Coefficient recovery, and hence construction injectivity, is an analytic result:
it uses a convergent series of continuous circle functions and the integral
Fourier coefficient map. No formal coefficient inverse is substituted for it.
-/

noncomputable section

namespace TorusLean.Geometry.ThetaFourier

open Complex Real ContinuousMap
open ThetaAnalytic ThetaFactorization
open scoped Interval

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def constructedCoefficients (d : ℕ) (tau sigma psi : ℂ) (v : ZMod d → ℂ) (n : ℤ) : ℂ :=
  physicalWeight d tau sigma psi n * v (n : ZMod d)

theorem constructedCoefficients_summable (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) :
    Summable (constructedCoefficients d tau sigma psi v) := by
  change Summable (fun n : ℤ => constructedCoefficients d tau sigma psi v n)
  have h := weightedFourierTerm_summable d tau sigma psi hτ v 0
  change Summable (fun n : ℤ => weightedFourierTerm d tau sigma psi v 0 n) at h
  simpa [weightedFourierTerm, constructedCoefficients] using h

theorem weightedTerm_untwist (d : ℕ) (tau sigma psi z : ℂ) (v : ZMod d → ℂ) (n : ℤ) :
    Complex.exp (-2 * π * I * sigma * z) * weightedFourierTerm d tau sigma psi v z n =
      constructedCoefficients d tau sigma psi v n * Complex.exp (2 * π * I * (n : ℂ) * z) := by
  unfold weightedFourierTerm constructedCoefficients
  calc
    _ = (physicalWeight d tau sigma psi n * v (n : ZMod d)) *
      (Complex.exp (-2 * π * I * sigma * z) *
        Complex.exp (2 * π * I * ((n : ℂ) + sigma) * z)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

/-- The untwisted constructed section on the real axis is exactly the
continuous-circle Fourier synthesis, rather than a merely formal sequence. -/
theorem realizedSection_real_axis (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) (t : ℝ) :
    untwist sigma (realizedSection d tau sigma psi v) (t : ℂ) =
      fourierSeries (constructedCoefficients d tau sigma psi v) (t : AddCircle (1 : ℝ)) := by
  have h := (weightedFourierTerm_hasSum d tau sigma psi hτ v (t : ℂ)).mul_left
    (Complex.exp (-2 * π * I * sigma * (t : ℂ)))
  change HasSum (fun n : ℤ => Complex.exp (-2 * π * I * sigma * (t : ℂ)) *
    weightedFourierTerm d tau sigma psi v (t : ℂ) n) _ at h
  simp_rw [weightedTerm_untwist] at h
  have hg := (ContinuousMap.evalCLM ℂ (t : AddCircle (1 : ℝ))).hasSum
    (fourierSeries_hasSum (constructedCoefficients d tau sigma psi v)
      (constructedCoefficients_summable d tau sigma psi hτ v))
  have hg' : HasSum (fun n : ℤ => constructedCoefficients d tau sigma psi v n *
      Complex.exp (2 * π * I * (n : ℂ) * (t : ℂ)))
      (fourierSeries (constructedCoefficients d tau sigma psi v) (t : AddCircle (1 : ℝ))) := by
    simpa [fourierSeriesTerm, fourier_coe_apply, smul_eq_mul] using hg
  exact h.unique hg'

/-- Identification of the real-cycle integral with the genuine circle Fourier
integral, whenever the entire untwisted real restriction equals `G`. -/
theorem fourierExtract_eq_circleCoeff (sigma : ℂ) (F : ℂ → ℂ)
    (G : C(AddCircle (1 : ℝ), ℂ))
    (hG : ∀ t : ℝ, untwist sigma F (t : ℂ) = G (t : AddCircle (1 : ℝ))) (n : ℤ) :
    fourierExtract sigma F n = fourierCoeff G n := by
  rw [fourierCoeff_eq_intervalIntegral G n (0 : ℝ)]
  simp only [one_div, inv_one, one_smul, zero_add]
  unfold fourierExtract
  apply intervalIntegral.integral_congr
  intro t _
  change Complex.exp (-2 * π * I * ((n : ℂ) + sigma) * (t : ℂ)) * F (t : ℂ) =
    fourier (-n) (t : AddCircle (1 : ℝ)) • G (t : AddCircle (1 : ℝ))
  rw [fourier_coe_apply, ← hG t]
  simp only [Complex.ofReal_one, div_one, smul_eq_mul, Int.cast_neg]
  unfold untwist
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Actual Fourier coefficient recovery at every integer mode. -/
theorem fourierExtract_realizedSection (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (v : ZMod d → ℂ) (n : ℤ) :
    fourierExtract sigma (realizedSection d tau sigma psi v) n =
      constructedCoefficients d tau sigma psi v n := by
  rw [fourierExtract_eq_circleCoeff sigma _ _
    (realizedSection_real_axis d tau sigma psi hτ v)]
  exact coefficient_fourierSeries _ (constructedCoefficients_summable d tau sigma psi hτ v) n

/-- Injectivity follows from actual coefficient integration of equal entire
functions. This does not assume exhaustion of arbitrary entire sections. -/
theorem realizedSection_injective (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) : Function.Injective (realizedSection d tau sigma psi) := by
  intro v u h
  funext r
  have hn := congrArg (fun F : ℂ → ℂ => fourierExtract sigma F (r.val : ℤ)) h
  rw [fourierExtract_realizedSection d tau sigma psi hτ v,
    fourierExtract_realizedSection d tau sigma psi hτ u] at hn
  have hw : physicalWeight d tau sigma psi (r.val : ℤ) ≠ 0 :=
    gaussianWeight_ne_zero d (π * I * tau) (-I * psi) sigma (r.val : ℤ)
  apply mul_left_cancel₀ hw
  simpa [constructedCoefficients] using hn

end TorusLean.Geometry.ThetaFourier
