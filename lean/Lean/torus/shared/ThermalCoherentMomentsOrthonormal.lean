import PlaneGaussianReproducing
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Exact cross-orthonormality of the original canonical plane jets in
full-plane dA/pi. The honest L2 domains come from CanonicalPlaneJets; the
accepted Gaussian derivative reproduction supplies the off-diagonal zero. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentMoments
open MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Fermion.CanonicalPlaneJets
open scoped ComplexConjugate ENNReal

/-- The original normalized jets, with both factorial factors retained. -/
theorem planeJet_cross_factor (j m : ℕ) (z : ℂ) :
    conj (planeJet j z) * planeJet m z =
      (Complex.exp (-(‖z‖^2 : ℂ)) * conj z^j * z^m) /
        ((Real.sqrt (j.factorial : ℝ) : ℂ) * (Real.sqrt (m.factorial : ℝ) : ℂ)) := by
  have hc : conj (gaussianFactor 1 z) = gaussianFactor 1 z := by
    rw [gaussianFactor_eq_norm, ← Complex.exp_conj, Complex.conj_ofReal]
  have hs : gaussianFactor 1 z * gaussianFactor 1 z =
      Complex.exp (-(‖z‖^2 : ℂ)) := by
    simp only [gaussianFactor_eq_norm]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [planeJet, map_div₀, map_mul, map_pow, hc, Complex.conj_ofReal]
  calc
    _ = ((gaussianFactor 1 z * gaussianFactor 1 z) * conj z^j * z^m) /
        ((Real.sqrt (j.factorial : ℝ) : ℂ) * (Real.sqrt (m.factorial : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hs]

theorem planeJet_cross_integrable (j m : ℕ) :
    Integrable (fun z => conj (planeJet j z) * planeJet m z) planeMeasure :=
  planeInner_integrable _ _ (planeJet_memLp j) (planeJet_memLp m)

/-- All j,m are genuinely orthonormal for the fixed original plane measure. -/
theorem planeJet_cross_integral (j m : ℕ) :
    (∫ z, conj (planeJet j z) * planeJet m z ∂planeMeasure) =
      if j=m then (1:ℂ) else 0 := by
  by_cases hjm : j=m
  · subst m
    simpa [planeInner] using planeJet_inner_self j
  · have hs (n : ℕ) : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
    have hw : Integrable (fun z : ℂ => Complex.exp (-(‖z‖^2 : ℂ)) * conj z^j * z^m)
        planeMeasure :=
      ((planeJet_cross_integrable j m).mul_const
        ((Real.sqrt (j.factorial : ℝ) : ℂ) * (Real.sqrt (m.factorial : ℝ) : ℂ))).congr
        (Filter.Eventually.of_forall fun z => by
          dsimp only
          rw [planeJet_cross_factor, div_mul_cancel₀ _ (mul_ne_zero (hs j) (hs m))])
    have hv : Integrable (fun z : ℂ => Complex.exp (-(‖z‖^2 : ℂ)) * conj z^j * z^m)
        volume := by
      rw [planeMeasure] at hw
      exact (integrable_smul_measure planeMeasure_scale_pos.ne' ENNReal.ofReal_ne_top).mp hw
    have hr := TorusLean.Fermion.PlaneGaussianReproducing.gaussian_reproducing_derivative
      j (fun z : ℂ => z^m) (by fun_prop) hv
    rw [iteratedDeriv_fun_pow_zero, if_neg hjm, Nat.cast_zero, mul_zero] at hr
    simp_rw [planeJet_cross_factor]
    rw [planeMeasure, integral_smul_measure, integral_div, hr]
    simp [hjm]

end TorusLean.Shared.ThermalCoherentMoments
