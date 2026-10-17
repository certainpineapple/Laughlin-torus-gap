import torus.shared.ThermalCoherentMoments

/-! Honest L1 absolute-cross control for summing coherent jet expansions.
The bound is obtained from true weighted L2 moments, not cancellation of
complex off-diagonal integrals. Infinite summation remains separate. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentMoments
open MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Fermion.CanonicalPlaneJets
open TorusLean.Shared.ThermalCoherentGaussian
open scoped ComplexConjugate ENNReal

theorem weighted_planeJet_norm_cross_integrable (a : ℝ) (ha : 0 < a) (j m : ℕ) :
    Integrable (fun z => thermalWeight a z * ‖planeJet j z‖ * ‖planeJet m z‖)
      planeMeasure := by
  apply (weighted_planeJet_cross_integrable a ha j m).norm.congr
  apply Filter.Eventually.of_forall
  intro z
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thermalWeight_pos a z), Complex.norm_conj]
  ring

theorem weighted_planeJet_sq_integrable (a : ℝ) (ha : 0 < a) (j : ℕ) :
    Integrable (fun z => thermalWeight a z * ‖planeJet j z‖^2) planeMeasure := by
  simpa only [pow_two, mul_assoc] using weighted_planeJet_norm_cross_integrable a ha j j

theorem weighted_planeJet_sq_integral (a : ℝ) (ha : 0 < a) (j : ℕ) :
    (∫ z, thermalWeight a z * ‖planeJet j z‖^2 ∂planeMeasure) = thermalEigenvalue a j := by
  have h := weighted_planeJet_cross_integral a ha j j
  have he (z : ℂ) : (thermalWeight a z : ℂ) *
      (conj (planeJet j z) * planeJet j z) =
        ((thermalWeight a z * ‖planeJet j z‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]
  simp_rw [he] at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by simpa using h)

private def halfWeightedNorm (a : ℝ) (j : ℕ) (z : ℂ) : ℝ :=
  Real.sqrt (thermalWeight a z) * ‖planeJet j z‖

private theorem halfWeightedNorm_nonneg (a : ℝ) (j : ℕ) (z : ℂ) :
    0 ≤ halfWeightedNorm a j z := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

private theorem halfWeightedNorm_sq (a : ℝ) (j : ℕ) (z : ℂ) :
    halfWeightedNorm a j z ^ 2 = thermalWeight a z * ‖planeJet j z‖^2 := by
  rw [halfWeightedNorm, mul_pow, Real.sq_sqrt (thermalWeight_pos a z).le]

private theorem halfWeightedNorm_memLp (a : ℝ) (ha : 0 < a) (j : ℕ) :
    MemLp (halfWeightedNorm a j) 2 planeMeasure := by
  have hc : Continuous (halfWeightedNorm a j) :=
    ((thermalWeight_continuous a).sqrt).mul (planeJet_continuous j).norm
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simpa only [Real.norm_eq_abs, sq_abs, halfWeightedNorm_sq] using
    weighted_planeJet_sq_integrable a ha j

/-- Absolute L1 cross control. This supplies the geometric-decay estimate
needed for a later justified infinite sum/integral interchange. -/
theorem weighted_planeJet_norm_cross_integral_le (a : ℝ) (ha : 0 < a) (j m : ℕ) :
    (∫ z, thermalWeight a z * ‖planeJet j z‖ * ‖planeJet m z‖ ∂planeMeasure) ≤
      Real.sqrt (thermalEigenvalue a j) * Real.sqrt (thermalEigenvalue a m) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (halfWeightedNorm_nonneg a j))
    (Filter.Eventually.of_forall (halfWeightedNorm_nonneg a m))
    (by simpa using halfWeightedNorm_memLp a ha j)
    (by simpa using halfWeightedNorm_memLp a ha m)
  have he (z : ℂ) : halfWeightedNorm a j z * halfWeightedNorm a m z =
      thermalWeight a z * ‖planeJet j z‖ * ‖planeJet m z‖ := by
    calc
      _ = (Real.sqrt (thermalWeight a z))^2 * ‖planeJet j z‖ * ‖planeJet m z‖ := by
        simp only [halfWeightedNorm]
        ring
      _ = _ := by rw [Real.sq_sqrt (thermalWeight_pos a z).le]
  simp only [he, Real.rpow_two, halfWeightedNorm_sq, weighted_planeJet_sq_integral a ha,
    ← Real.sqrt_eq_rpow] at h
  exact h

end TorusLean.Shared.ThermalCoherentMoments
