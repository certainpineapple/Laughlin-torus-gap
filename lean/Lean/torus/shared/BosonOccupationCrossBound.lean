import torus.boson.PolynomialInnerAdjoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Tactic.Linarith

/-! Cauchy--Schwarz and Young for the actual finite occupation form.
Zero coordinate scales are allowed. The proof uses a positive semidefinite
form, without assuming a Hilbert completion or changing the polynomial core. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonOccupationCrossBound
open TorusLean.Boson
open scoped ComplexConjugate
variable {ι : Type*} [Fintype ι]

private def occupationPreInner (scale : ι → ℕ) :
    PreInnerProductSpace.Core ℂ (Core ι ℂ) where
  inner := occupationInner scale
  conj_inner_symm f g := occupationInner_conj_symm scale g f
  re_inner_nonneg := occupationInner_self_nonneg scale
  add_left := occupationInner_add_left scale
  smul_left f g c := occupationInner_smul_left scale c f g

/-- Genuine complex Cauchy--Schwarz, including degenerate scales. -/
theorem occupationInner_norm_le_sqrt (scale : ι → ℕ) (f g : Core ι ℂ) :
    ‖occupationInner scale f g‖ ≤
      Real.sqrt (occupationMetricNormSq scale f) *
        Real.sqrt (occupationMetricNormSq scale g) := by
  letI := occupationPreInner scale
  have h := InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℂ) f g
  change ‖occupationInner scale f g‖ ≤
    Real.sqrt (occupationInner scale f f).re *
      Real.sqrt (occupationInner scale g g).re at h
  simpa only [occupationInner_self_re] using h

/-- Squared cross bound in the unchanged occupation metric. -/
theorem occupationInner_norm_sq_le (scale : ι → ℕ) (f g : Core ι ℂ) :
    ‖occupationInner scale f g‖ ^ 2 ≤
      occupationMetricNormSq scale f * occupationMetricNormSq scale g := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (occupationInner_norm_le_sqrt scale f g) 2
  simpa only [mul_pow, Real.sq_sqrt (occupationMetricNormSq_nonneg scale f),
    Real.sq_sqrt (occupationMetricNormSq_nonneg scale g)] using h

/-- Sharp unweighted complex Young bound. -/
theorem occupationInner_norm_young (scale : ι → ℕ) (f g : Core ι ℂ) :
    2 * ‖occupationInner scale f g‖ ≤
      occupationMetricNormSq scale f + occupationMetricNormSq scale g := by
  have h := occupationInner_norm_le_sqrt scale f g
  have hf := Real.sq_sqrt (occupationMetricNormSq_nonneg scale f)
  have hg := Real.sq_sqrt (occupationMetricNormSq_nonneg scale g)
  nlinarith [sq_nonneg (Real.sqrt (occupationMetricNormSq scale f) -
    Real.sqrt (occupationMetricNormSq scale g))]

/-- A convenient L1 domination by positive row energies. -/
theorem occupationInner_norm_le_sum (scale : ι → ℕ) (f g : Core ι ℂ) :
    ‖occupationInner scale f g‖ ≤
      occupationMetricNormSq scale f + occupationMetricNormSq scale g := by
  have h := occupationInner_norm_young scale f g
  linarith [norm_nonneg (occupationInner scale f g)]

#print axioms occupationInner_norm_le_sqrt
#print axioms occupationInner_norm_sq_le
#print axioms occupationInner_norm_young
#print axioms occupationInner_norm_le_sum
end TorusLean.Shared.BosonOccupationCrossBound
