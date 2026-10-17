import torus.shared.ThermalCoherentMomentsOrthonormal
import torus.shared.ThermalCoherentGaussian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Exact thermal spectral moments of the original plane jets. Offsets range
over the entire complex plane with dA/pi. Both integrability and the actual
2D scaling Jacobian are proved before any use of finite-sum diagonalization.
No infinite sum, coherent transfer or Omega identity is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentMoments
open MeasureTheory TorusLean.Geometry
open TorusLean.Fermion.PlaneMagneticUnitary
open TorusLean.Shared.ThermalCoherentGaussian
open scoped ComplexConjugate ENNReal BigOperators

private instance planeMeasure_isAddHaar : Measure.IsAddHaarMeasure planeMeasure := by
  unfold planeMeasure
  exact Measure.IsAddHaarMeasure.smul volume planeMeasure_scale_pos.ne' ENNReal.ofReal_ne_top

/-- Exact eigenvalue for an exp(-a |beta|^2) weight against normalized e_j. -/
def thermalEigenvalue (a : ℝ) (j : ℕ) : ℝ := ((1+a)^(j+1))⁻¹

theorem thermalEigenvalue_pos (a : ℝ) (ha : 0 < a) (j : ℕ) :
    0 < thermalEigenvalue a j := by unfold thermalEigenvalue; positivity

/-- Genuine pointwise dilation, including both jet powers and their Gaussian. -/
theorem weighted_cross_dilation (a : ℝ) (ha : 0 < a) (j m : ℕ) (z : ℂ) :
    (thermalWeight a z : ℂ) * (conj (planeJet j z) * planeJet m z) =
      ((Real.sqrt (1+a) : ℂ)^(j+m))⁻¹ *
        (conj (planeJet j (Real.sqrt (1+a) • z)) *
          planeJet m (Real.sqrt (1+a) • z)) := by
  have hr : 0 < Real.sqrt (1+a) := Real.sqrt_pos.mpr (by positivity)
  have hrsq : (Real.sqrt (1+a))^2 = 1+a := Real.sq_sqrt (by positivity)
  have hn : ‖Real.sqrt (1+a) • z‖^2 = (1+a)*‖z‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow, hrsq]
  have hnc : (‖Real.sqrt (1+a) • z‖ : ℂ)^2 = ((1+a : ℝ) : ℂ)*(‖z‖ : ℂ)^2 := by
    exact_mod_cast hn
  have he : (thermalWeight a z : ℂ) * Complex.exp (-(‖z‖^2 : ℂ)) =
      Complex.exp (-(‖Real.sqrt (1+a) • z‖^2 : ℂ)) := by
    rw [thermalWeight, Complex.ofReal_exp, ← Complex.exp_add, hnc]
    congr 1
    push_cast
    ring
  have hc : conj (planeJet j (Real.sqrt (1+a) • z)) *
      planeJet m (Real.sqrt (1+a) • z) =
        (Real.sqrt (1+a) : ℂ)^(j+m) *
          ((thermalWeight a z : ℂ) * (conj (planeJet j z) * planeJet m z)) := by
    rw [planeJet_cross_factor, planeJet_cross_factor, ← he]
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, mul_pow, pow_add]
    ring
  rw [hc, inv_mul_cancel_left₀]
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')

/-- Weighted cross terms are really Bochner integrable, not inferred from a
possibly totalized zero integral. Dilation preserves integrability. -/
theorem weighted_planeJet_cross_integrable (a : ℝ) (ha : 0 < a) (j m : ℕ) :
    Integrable (fun z => (thermalWeight a z : ℂ) *
      (conj (planeJet j z) * planeJet m z)) planeMeasure := by
  have hr : Real.sqrt (1+a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have h := ((planeJet_cross_integrable j m).comp_smul hr).const_mul
    (((Real.sqrt (1+a) : ℂ)^(j+m))⁻¹)
  exact h.congr (Filter.Eventually.of_forall fun z => (weighted_cross_dilation a ha j m z).symm)

/-- The exact thermal spectrum, using the real two-dimensional Jacobian. -/
theorem weighted_planeJet_cross_integral (a : ℝ) (ha : 0 < a) (j m : ℕ) :
    (∫ z, (thermalWeight a z : ℂ) *
      (conj (planeJet j z) * planeJet m z) ∂planeMeasure) =
        if j=m then (thermalEigenvalue a j : ℂ) else 0 := by
  simp_rw [weighted_cross_dilation a ha j m]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg planeMeasure
    (fun z => conj (planeJet j z) * planeJet m z) (Real.sqrt (1+a))
    (hR := Real.sqrt_nonneg _), Complex.finrank_real_complex,
    Real.sq_sqrt (by positivity : 0 ≤ 1+a), planeJet_cross_integral]
  by_cases hjm : j=m
  · subst m
    rw [if_pos rfl, Complex.real_smul, mul_one]
    have hp : (Real.sqrt (1+a) : ℂ)^(j+j) = ((1+a : ℝ) : ℂ)^j := by
      rw [← two_mul, pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    rw [hp]
    simp only [thermalEigenvalue, ite_true, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_pow, pow_succ, mul_inv]
  · simp [hjm]

/-- Any genuinely finite coefficient matrix diagonalizes against the same
positive plane Gaussian; no exchange of an infinite sum and integral occurs. -/
theorem finite_matrix_thermal_integral (a : ℝ) (ha : 0 < a) (s : Finset ℕ)
    (M : ℕ → ℕ → ℂ) :
    (∫ z, ∑ j ∈ s, ∑ m ∈ s, M j m * ((thermalWeight a z : ℂ) *
      (conj (planeJet j z) * planeJet m z)) ∂planeMeasure) =
        ∑ j ∈ s, M j j * (thermalEigenvalue a j : ℂ) := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul, weighted_planeJet_cross_integral a ha]
      simp [hj]
    · intro m hm
      exact (weighted_planeJet_cross_integrable a ha j m).const_mul (M j m)
  · intro j hj
    exact integrable_finset_sum _ (fun m hm =>
      (weighted_planeJet_cross_integrable a ha j m).const_mul (M j m))

end TorusLean.Shared.ThermalCoherentMoments
