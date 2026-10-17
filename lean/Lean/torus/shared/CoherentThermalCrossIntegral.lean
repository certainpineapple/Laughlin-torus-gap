import torus.shared.CoherentThermalSummability
import torus.shared.ThermalCoherentMomentsNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolute L1 control of the two-index coherent expansion.  The moment
cancellation is used only after the series of absolute integrals is proved
summable.  The physical coefficients will discharge the stated coefficient
budgets using CoherentThermalSummability. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.CoherentThermalCrossIntegral
open MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.CanonicalPlaneJets
open TorusLean.Shared.ThermalCoherentGaussian TorusLean.Shared.ThermalCoherentMoments
open TorusLean.Shared.CoherentThermalSummability
open scoped ComplexConjugate

def thermalCrossTerm (a : ℝ) (A B : ℕ → ℂ) (jm : ℕ × ℕ) (beta : ℂ) : ℂ :=
  (thermalWeight a beta : ℂ) * (conj (planeJet jm.2 beta) * planeJet jm.1 beta) *
    (conj (A jm.1) * B jm.2)

theorem thermalCrossTerm_integrable (a : ℝ) (ha : 0 < a) (A B : ℕ → ℂ)
    (jm : ℕ × ℕ) : Integrable (thermalCrossTerm a A B jm) planeMeasure :=
  (weighted_planeJet_cross_integrable a ha jm.2 jm.1).mul_const _

theorem thermalCrossTerm_integral (a : ℝ) (ha : 0 < a) (A B : ℕ → ℂ)
    (jm : ℕ × ℕ) :
    (∫ beta, thermalCrossTerm a A B jm beta ∂planeMeasure) =
      if jm.1 = jm.2 then (thermalEigenvalue a jm.1 : ℂ) * conj (A jm.1) * B jm.2 else 0 := by
  simp only [thermalCrossTerm]
  rw [integral_mul_const, weighted_planeJet_cross_integral a ha]
  split_ifs with h h' h'
  · rw [h]
    ring
  · exact False.elim (h' h.symm)
  · exact False.elim (h h'.symm)
  · simp

theorem thermalCrossTerm_integral_norm_le (a : ℝ) (ha : 0 < a) (A B : ℕ → ℂ)
    (jm : ℕ × ℕ) :
    (∫ beta, ‖thermalCrossTerm a A B jm beta‖ ∂planeMeasure) ≤
      (thermalRootRatio a ^ (jm.1+1) * ‖A jm.1‖) *
        (thermalRootRatio a ^ (jm.2+1) * ‖B jm.2‖) := by
  have he (beta : ℂ) : ‖thermalCrossTerm a A B jm beta‖ =
      (thermalWeight a beta * ‖planeJet jm.2 beta‖ * ‖planeJet jm.1 beta‖) *
        (‖A jm.1‖ * ‖B jm.2‖) := by
    simp only [thermalCrossTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (thermalWeight_pos a beta), Complex.norm_conj]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  calc
    _ ≤ (Real.sqrt (thermalEigenvalue a jm.2) * Real.sqrt (thermalEigenvalue a jm.1)) *
        (‖A jm.1‖ * ‖B jm.2‖) :=
      mul_le_mul_of_nonneg_right (weighted_planeJet_norm_cross_integral_le a ha jm.2 jm.1)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [thermalEigenvalue, sqrt_thermalEigenvalue a ha]
      ring

/-- Absolute integrals are summable in the full product index set. -/
theorem thermalCrossTerm_summable_integral_norm (a : ℝ) (ha : 0 < a) (A B : ℕ → ℂ)
    (hA : Summable (fun j => thermalRootRatio a ^ (j+1) * ‖A j‖))
    (hB : Summable (fun j => thermalRootRatio a ^ (j+1) * ‖B j‖)) :
    Summable (fun jm : ℕ × ℕ => ∫ beta, ‖thermalCrossTerm a A B jm beta‖ ∂planeMeasure) := by
  have hn (C : ℕ → ℂ) (j : ℕ) : 0 ≤ thermalRootRatio a ^ (j+1) * ‖C j‖ :=
    mul_nonneg (pow_nonneg (thermalRootRatio_pos_lt_one a ha).1.le _) (norm_nonneg _)
  exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (thermalCrossTerm_integral_norm_le a ha A B) (hA.mul_of_nonneg hB (hn A) (hn B))

/-- A justified exchange of the infinite double series and the full-plane
thermal integral.  No off-diagonal cancellation supplies its hypotheses. -/
theorem thermalCrossTerm_integral_hasSum (a : ℝ) (ha : 0 < a) (A B : ℕ → ℂ)
    (hA : Summable (fun j => thermalRootRatio a ^ (j+1) * ‖A j‖))
    (hB : Summable (fun j => thermalRootRatio a ^ (j+1) * ‖B j‖)) :
    HasSum (fun jm : ℕ × ℕ => ∫ beta, thermalCrossTerm a A B jm beta ∂planeMeasure)
      (∫ beta, ∑' jm : ℕ × ℕ, thermalCrossTerm a A B jm beta ∂planeMeasure) :=
  hasSum_integral_of_summable_integral_norm (thermalCrossTerm_integrable a ha A B)
    (thermalCrossTerm_summable_integral_norm a ha A B hA hB)

end TorusLean.Shared.CoherentThermalCrossIntegral
