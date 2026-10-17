import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Controlled positive series integration. Actual integrability of the
pointwise sum is an explicit domain requirement, not deduced from a
potentially totalized integral. Physical modules discharge that domain. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentSpectralIntegral
open MeasureTheory

variable {X J : Type*} [MeasurableSpace X] [Countable J]
    (μ : Measure X) (f : J → X → ℝ) (F : X → ℝ)

/-- Every nonnegative term is dominated by its genuinely integrable sum. -/
theorem nonnegative_hasSum_term_integrable
    (hnon : ∀ j x, 0 ≤ f j x) (hmeas : ∀ j, AEStronglyMeasurable (f j) μ)
    (hpoint : ∀ x, HasSum (fun j => f j x) (F x)) (hF : Integrable F μ) (j : J) :
    Integrable (f j) μ := by
  apply hF.mono' (hmeas j)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (hnon j x)]
  exact le_hasSum (hpoint x) j (fun k hk => hnon k x)

/-- Nonnegative Tonelli/dominated-series transport with a finite actual sum
integral. This establishes HasSum, not only equality of totalized integrals. -/
theorem integral_hasSum_of_nonnegative_hasSum
    (hnon : ∀ j x, 0 ≤ f j x) (hmeas : ∀ j, AEStronglyMeasurable (f j) μ)
    (hpoint : ∀ x, HasSum (fun j => f j x) (F x)) (hF : Integrable F μ) :
    HasSum (fun j => ∫ x, f j x ∂μ) (∫ x, F x ∂μ) := by
  have he : (fun x => ∑' j, f j x) = F := funext fun x => (hpoint x).tsum_eq
  apply hasSum_integral_of_dominated_convergence f hmeas
  · intro j
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnon j x)]
  · exact Filter.Eventually.of_forall fun x => (hpoint x).summable
  · rwa [he]
  · exact Filter.Eventually.of_forall hpoint

end TorusLean.Shared.ThermalCoherentSpectralIntegral
