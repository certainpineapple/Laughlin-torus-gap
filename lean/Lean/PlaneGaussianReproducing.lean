import CanonicalPlaneJets
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The Gaussian reproducing calculation needed for canonical planeJets.
The only input domains are actual holomorphy and integrability of the
Gaussian-weighted function. No displacement or jet envelope is assumed. -/

set_option autoImplicit false

namespace TorusLean.Fermion.PlaneGaussianReproducing

open MeasureTheory Complex Set
open scoped ComplexConjugate BigOperators ENNReal

noncomputable section

theorem angular_moment (j : ℕ) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (r : ℝ) (hr : 0 < r) :
    (∫ theta in 0..2*Real.pi, conj (circleMap 0 r theta)^j * F (circleMap 0 r theta)) =
      ((2*Real.pi : ℂ) * (r : ℂ)^(2*j) / (j.factorial : ℂ)) *
        iteratedDeriv j F 0 := by
  have hc := hF.differentiableOn.circleIntegral_one_div_sub_center_pow_smul hr j
    (c := (0 : ℂ))
  have heq : (∫ theta in 0..2*Real.pi,
      conj (circleMap 0 r theta)^j * F (circleMap 0 r theta)) =
      (-I * (r : ℂ)^(2*j)) *
        (∮ z in C(0, r), (1 / (z - 0)^(j+1)) • F z) := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro theta htheta
    simp only [deriv_circleMap, sub_zero, smul_eq_mul]
    have hz : circleMap 0 r theta ≠ 0 := by
      simp [circleMap_zero, ne_of_gt hr]
    have hnorm : circleMap 0 r theta * conj (circleMap 0 r theta) = (r : ℂ)^2 := by
      rw [Complex.mul_conj', norm_circleMap_zero, abs_of_pos hr]
    have hp := congrArg (fun z : ℂ => z^j) hnorm
    simp only [mul_pow, ← pow_mul] at hp
    rw [pow_succ]
    field_simp
    rw [← hp]
    simp only [Complex.I_sq]
    ring
  rw [heq, hc]
  simp only [smul_eq_mul]
  rw [show -I * (r : ℂ)^(2*j) * ((2*Real.pi*I/(j.factorial : ℂ))*
      iteratedDeriv j F 0) =
      (-I*I) * ((2*Real.pi : ℂ)*(r : ℂ)^(2*j)/(j.factorial : ℂ)) *
        iteratedDeriv j F 0 by ring]
  simp

private theorem polar_symm_continuous : Continuous Complex.polarCoord.symm := by
  have h : Complex.polarCoord.symm = fun p : ℝ × ℝ =>
      (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) := by
    funext p
    exact Complex.polarCoord_symm_apply p
  rw [h]
  exact
    (Complex.continuous_ofReal.comp continuous_fst).mul
      ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_snd)).add
        ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_snd)).mul
          (continuous_const (y := I))))

/-- The actual polar Jacobian preserves integrability of a continuous
complex-valued function; derived from Mathlib's positive change of variables. -/
theorem polar_integrable (f : ℂ → ℂ) (hc : Continuous f)
    (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
  constructor
  · exact (continuous_fst.smul (hc.comp polar_symm_continuous)).aestronglyMeasurable
  · have hf' := hf.2
    rw [hasFiniteIntegral_iff_norm] at hf' ⊢
    have heq : (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal ‖p.1 • f (Complex.polarCoord.symm p)‖) =
        ∫⁻ z : ℂ, ENNReal.ofReal ‖f z‖ := by
      rw [← Complex.lintegral_comp_polarCoord_symm]
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hp0 : 0 < p.1 := mem_Ioi.mp hp.1
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hp0,
        ENNReal.ofReal_mul hp0.le, smul_eq_mul]
    rw [heq]
    exact hf'

private theorem polar_symm_circle (r theta : ℝ) :
    Complex.polarCoord.symm (r, theta) = circleMap 0 r theta := by
  rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_ofReal_mul_I]

private theorem angular_moment_polar (j : ℕ) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (r : ℝ) (hr : 0 < r) :
    (∫ theta in Ioo (-Real.pi) Real.pi,
      conj (Complex.polarCoord.symm (r, theta))^j *
        F (Complex.polarCoord.symm (r, theta))) =
      ((2*Real.pi : ℂ)*(r : ℂ)^(2*j)/(j.factorial : ℂ))*iteratedDeriv j F 0 := by
  simp_rw [polar_symm_circle]
  have hper := (periodic_circleMap 0 r).comp (fun z : ℂ => conj z^j * F z)
  have hshift := hper.intervalIntegral_add_eq (-Real.pi) 0
  simp only [show -Real.pi + 2*Real.pi = Real.pi by ring, zero_add,
    Function.comp_apply] at hshift
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), hshift]
  exact angular_moment j F hF r hr

private theorem radial_moment (j : ℕ) :
    (∫ r in Ioi (0 : ℝ), r^(2*j+1)*Real.exp (-r^2)) = (j.factorial : ℝ)/2 := by
  have h := _root_.integral_rpow_mul_exp_neg_rpow (p := (2 : ℝ))
    (q := (2*j+1 : ℕ)) (by norm_num)
    (by nlinarith [(Nat.cast_nonneg (2*j+1) : (0 : ℝ) ≤ (2*j+1 : ℕ))])
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  rw [show (((2*j+1 : ℕ) : ℝ)+1)/2 = (j : ℝ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial] at h
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using h

/-- Gaussian reproducing derivative, on honest entire/integrable domains.
The volume is ordinary real two-dimensional Lebesgue measure. -/
theorem gaussian_reproducing_derivative (j : ℕ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hf : Integrable (fun z : ℂ => Complex.exp (-(‖z‖^2 : ℂ))*conj z^j*F z)) :
    (∫ z : ℂ, Complex.exp (-(‖z‖^2 : ℂ))*conj z^j*F z) =
      (Real.pi : ℂ)*iteratedDeriv j F 0 := by
  let f : ℂ → ℂ := fun z => Complex.exp (-(‖z‖^2 : ℂ))*conj z^j*F z
  have hc : Continuous f := by
    have hFc := hF.continuous
    dsimp [f]
    fun_prop
  have hpolar := polar_integrable f hc hf
  rw [Complex.polarCoord_target, Measure.volume_eq_prod] at hpolar
  rw [← Complex.integral_comp_polarCoord_symm]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • (Complex.exp (-(‖Complex.polarCoord.symm p‖^2 : ℂ))*
      conj (Complex.polarCoord.symm p)^j*F (Complex.polarCoord.symm p))) = _
  rw [Measure.volume_eq_prod, setIntegral_prod _ hpolar]
  calc
    _ = ∫ r in Ioi (0 : ℝ),
        (r : ℂ)*Complex.exp (-(r^2 : ℂ)) *
          (((2*Real.pi : ℂ)*(r : ℂ)^(2*j)/(j.factorial : ℂ))*
            iteratedDeriv j F 0) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr0 : 0 < r := mem_Ioi.mp hr
      dsimp only [f]
      rw [← angular_moment_polar j F hF r hr0, ← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro theta
      simp only [Complex.real_smul, Complex.norm_polarCoord_symm, abs_of_pos hr0]
      ring
    _ = ((∫ r in Ioi (0 : ℝ), r^(2*j+1)*Real.exp (-r^2) : ℝ) : ℂ) *
        ((2*Real.pi : ℂ)/(j.factorial : ℂ)*iteratedDeriv j F 0) := by
      rw [← integral_complex_ofReal, ← integral_mul_const]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro r
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp,
        Complex.ofReal_neg, pow_succ]
      ring
    _ = _ := by
      rw [radial_moment]
      push_cast
      have hf0 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
      field_simp


end
end TorusLean.Fermion.PlaneGaussianReproducing
