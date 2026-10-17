import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false

/-!
Fourier synthesis and coefficient recovery on the real circle of period one.
Summable coefficients produce a convergent series in the sup norm on continuous
functions. Coefficient recovery uses the actual Haar-integral Fourier coefficients,
through the audited Fourier Hilbert basis and the continuous map into `L²`.

The final uniqueness theorem applies to every continuous function on this circle;
it does not assume that its Fourier coefficients are summable.
-/

noncomputable section

namespace TorusLean.Geometry.ThetaFourier

open Complex ContinuousMap MeasureTheory
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def fourierSeriesTerm (c : ℤ → ℂ) (n : ℤ) : C(AddCircle (1 : ℝ), ℂ) :=
  c n • fourier n

def fourierSeries (c : ℤ → ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  ∑' n : ℤ, fourierSeriesTerm c n

theorem fourierSeriesTerm_norm (c : ℤ → ℂ) (n : ℤ) :
    ‖fourierSeriesTerm c n‖ = ‖c n‖ := by
  simp only [fourierSeriesTerm, norm_smul, fourier_norm, mul_one]

theorem fourierSeries_summable (c : ℤ → ℂ) (hc : Summable c) :
    Summable (fourierSeriesTerm c) := by
  apply Summable.of_norm
  simpa only [fourierSeriesTerm_norm] using hc.norm

theorem fourierSeries_hasSum (c : ℤ → ℂ) (hc : Summable c) :
    HasSum (fourierSeriesTerm c) (fourierSeries c) :=
  (fourierSeries_summable c hc).hasSum

theorem fourierSeries_hasSum_apply (c : ℤ → ℂ) (hc : Summable c)
    (x : AddCircle (1 : ℝ)) :
    HasSum (fun n : ℤ => c n * fourier n x) (fourierSeries c x) := by
  simpa only [fourierSeriesTerm, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
    smul_eq_mul] using (ContinuousMap.evalCLM ℂ x).hasSum (fourierSeries_hasSum c hc)

theorem fourierSeries_apply (c : ℤ → ℂ) (hc : Summable c) (x : AddCircle (1 : ℝ)) :
    fourierSeries c x = ∑' n : ℤ, c n * fourier n x :=
  (fourierSeries_hasSum_apply c hc x).tsum_eq.symm

theorem fourierSeries_apply_real (c : ℤ → ℂ) (hc : Summable c) (x : ℝ) :
    fourierSeries c (x : AddCircle (1 : ℝ)) =
      ∑' n : ℤ, c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) := by
  rw [fourierSeries_apply c hc]
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]

/-- Fourier coefficient extraction is a continuous complex-linear map. Its
identification with the actual coefficient integral is proved immediately below. -/
def continuousFourierCoeffCLM (n : ℤ) : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    ((fourierBasis (T := (1 : ℝ))).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) ℂ))

theorem continuousFourierCoeffCLM_apply (n : ℤ) (F : C(AddCircle (1 : ℝ), ℂ)) :
    continuousFourierCoeffCLM n F = fourierCoeff F n := by
  change fourierBasis.repr
    (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F) n = _
  rw [fourierBasis_repr, fourierCoeff_toLp]

theorem coefficient_fourierSeriesTerm (c : ℤ → ℂ) (k n : ℤ) :
    fourierCoeff (fourierSeriesTerm c k) n = if k = n then c n else 0 := by
  change fourierCoeff (c k • (fourier k : AddCircle (1 : ℝ) → ℂ)) n = _
  rw [fourierCoeff.const_smul, fourierCoeff_fourier]
  by_cases h : k = n
  · subst k
    simp
  · simp [h, Ne.symm h]

/-- Actual integral coefficients of the uniformly convergent Fourier synthesis
recover the original summable sequence, at every integer index. -/
theorem coefficient_fourierSeries (c : ℤ → ℂ) (hc : Summable c) (n : ℤ) :
    fourierCoeff (fourierSeries c) n = c n := by
  have h := (continuousFourierCoeffCLM n).hasSum (fourierSeries_hasSum c hc)
  simp only [continuousFourierCoeffCLM_apply, coefficient_fourierSeriesTerm] at h
  exact h.unique (hasSum_ite_eq n (c n))

/-- Every continuous function on the period-one circle is uniquely determined
by its integral Fourier coefficients. No summability assumption is required. -/
theorem continuous_eq_of_fourierCoeff_eq (F G : C(AddCircle (1 : ℝ), ℂ))
    (h : ∀ n : ℤ, fourierCoeff F n = fourierCoeff G n) : F = G := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  apply fourierBasis.repr.injective
  ext n
  simpa only [fourierBasis_repr, fourierCoeff_toLp] using h n

theorem fourierSeries_injective_of_summable (c b : ℤ → ℂ)
    (hc : Summable c) (hb : Summable b) (h : fourierSeries c = fourierSeries b) : c = b := by
  funext n
  have hn := congrArg (fun F : C(AddCircle (1 : ℝ), ℂ) => fourierCoeff F n) h
  simpa only [coefficient_fourierSeries c hc, coefficient_fourierSeries b hb] using hn

end TorusLean.Geometry.ThetaFourier
