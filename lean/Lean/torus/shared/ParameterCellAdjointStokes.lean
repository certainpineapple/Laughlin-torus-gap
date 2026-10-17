import torus.shared.ParameterCellAdjointDefinitions
import torus.shared.CellTranslation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Stokes on the actual half-open magnetic cell, proved by translating its
fundamental domain and differentiating only under an explicit compact bound. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterCellAdjoint
open MeasureTheory Set Filter
open scoped Topology Pointwise ComplexConjugate

/-- Every real Frechet derivative of a C1 periodic function has zero
integral on the original physical cell. The compact-neighborhood estimate
justifies the derivative/integral interchange. -/
theorem periodic_cell_integral_fderiv_zero (G : Geometry) (k : ℕ)
    (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F)
    (hperiodic : ∀ p : ℤ × ℤ, ∀ z : ℂ,
      F (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z) = F z) :
    (∫ z, fderiv ℝ F z ∂cellMeasure G k) = 0 := by
  have hDF : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  let K : Set ℂ := closedCell G + Metric.closedBall (0 : ℂ) 1
  have hK : IsCompact K := (isCompact_closedCell G).add (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hDF.continuousOn
  have hmem : ∀ᵐ z ∂cellMeasure G k, z ∈ cell G := by
    exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_cell G)) _
  have hb : ∀ᵐ z ∂cellMeasure G k, ∀ x ∈ Metric.ball (0 : ℂ) 1,
      ‖fderiv ℝ F (z+x)‖ ≤ C := by
    filter_upwards [hmem] with z hz x hx
    apply hC
    exact Set.mem_add.mpr ⟨z, cell_subset_closedCell G hz, x,
      Metric.ball_subset_closedBall hx, rfl⟩
  have hd (z x : ℂ) : HasFDerivAt (fun y : ℂ => F (z+y)) (fderiv ℝ F (z+x)) x := by
    simpa using! ((hF.differentiable one_ne_zero) (z+x)).hasFDerivAt.comp x
      ((hasFDerivAt_const z x).add (hasFDerivAt_id x))
  have hint := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x z : ℂ => F (z+x)) (F' := fun x z => fderiv ℝ F (z+x))
    (μ := cellMeasure G k) (bound := fun _ => C)
    (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
    (Eventually.of_forall (fun x => (hF.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable))
    (by simpa only [add_zero] using continuous_integrable_cellMeasure G k hF.continuous)
    (by simpa only [add_zero] using hDF.aestronglyMeasurable (μ := cellMeasure G k))
    hb (integrable_const C) (Eventually.of_forall (fun z x _ => hd z x))
  simp only [add_zero] at hint
  have heq : (fun x : ℂ => ∫ z, F (z+x) ∂cellMeasure G k) =
      (fun _ : ℂ => ∫ z, F z ∂cellMeasure G k) :=
    funext (CellTranslation.periodic_cellIntegral_translate G k F hperiodic)
  rw [heq] at hint
  exact hint.unique (hasFDerivAt_const _ _)

theorem periodic_cell_integral_direction_zero (G : Geometry) (k : ℕ)
    (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F)
    (hperiodic : ∀ p : ℤ × ℤ, ∀ z : ℂ,
      F (TorusLean.Geometry.latticePeriod G.omega1 G.omega2 p + z) = F z)
    (v : ℂ) :
    (∫ z, (fderiv ℝ F z) v ∂cellMeasure G k) = 0 := by
  rw [← ContinuousLinearMap.integral_apply
    (continuous_integrable_cellMeasure G k (hF.continuous_fderiv one_ne_zero)),
    periodic_cell_integral_fderiv_zero G k F hF hperiodic]
  rfl

end TorusLean.Shared.ParameterCellAdjoint
