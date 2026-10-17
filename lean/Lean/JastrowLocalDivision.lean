import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

/-!
Local division in one complex variable, derived from the original vanishing
jets. The analytic quotient is a conclusion, including the case that the
numerator vanishes identically near the point.

These statements do not establish joint analytic division in several variables
or division by a product of pair-diagonal factors at an intersection.
-/

namespace TorusLean.Geometry.JastrowDivision

open Filter
open scoped Topology

/-- Vanishing of the first `m` derivative jets yields a genuine analytic
quotient by `(z - a) ^ m` in a neighborhood of `a`. -/
theorem local_pow_division_of_jets (f : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (hf : AnalyticAt ℂ f a) (hjets : ∀ j < m, iteratedDeriv j f a = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q a ∧
      ∀ᶠ z in 𝓝 a, f z = (z - a) ^ m * q z := by
  have horder : (m : ℕ∞) ≤ analyticOrderAt f a :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr hjets
  obtain ⟨q, hq, hfactor⟩ := (natCast_le_analyticOrderAt hf).mp horder
  exact ⟨q, hq, by simpa only [smul_eq_mul] using hfactor⟩

/-- A simple zero has a nonvanishing analytic unit after removing `z - a`. -/
theorem local_simple_zero_factor (g : ℂ → ℂ) (a : ℂ) (hg : AnalyticAt ℂ g a)
    (hgzero : g a = 0) (hgderiv : deriv g a ≠ 0) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧ u a ≠ 0 ∧
      ∀ᶠ z in 𝓝 a, g z = (z - a) * u z := by
  have horder : analyticOrderAt g a = (1 : ℕ∞) :=
    hg.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hgzero hgderiv
  obtain ⟨u, hu, hu0, hfactor⟩ := (hg.analyticOrderAt_eq_natCast (n := 1)).mp horder
  exact ⟨u, hu, hu0, by simpa only [pow_one, smul_eq_mul] using hfactor⟩

/-- Original vanishing jets also yield local analytic division by a power of
any analytic divisor with a simple zero. No quotient is assumed. -/
theorem local_simple_divisor_pow_division_of_jets (f g : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (hf : AnalyticAt ℂ f a) (hjets : ∀ j < m, iteratedDeriv j f a = 0)
    (hg : AnalyticAt ℂ g a) (hgzero : g a = 0) (hgderiv : deriv g a ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q a ∧
      ∀ᶠ z in 𝓝 a, f z = (g z) ^ m * q z := by
  obtain ⟨q, hq, hfq⟩ := local_pow_division_of_jets f a m hf hjets
  obtain ⟨u, hu, hu0, hgu⟩ := local_simple_zero_factor g a hg hgzero hgderiv
  refine ⟨fun z => q z / (u z) ^ m, hq.div (hu.pow m) (pow_ne_zero m hu0), ?_⟩
  filter_upwards [hfq, hgu, hu.continuousAt.eventually_ne hu0] with z hfz hgz huz
  rw [hgz, mul_pow, mul_assoc, mul_div_cancel₀ _ (pow_ne_zero m huz)]
  exact hfz

end TorusLean.Geometry.JastrowDivision
