import CanonicalPlaneJets
import LaguerreEnvelope
import PlaneGaussianReproducing
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Actual canonical displacement integrands and complex Gaussian integrals.
The magnetic convention, Gaussian, planeJet and d²z/pi measure are reused.
No Laguerre displacement identity is an input hypothesis. -/

set_option autoImplicit false

namespace TorusLean.Fermion.PlaneJetDisplacement

open MeasureTheory TorusLean.Geometry PlaneMagneticUnitary CanonicalPlaneJets
open scoped ComplexConjugate BigOperators ENNReal

noncomputable section

private theorem norm_sq_real_coords (z : ℂ) : ‖z‖^2 = z.re^2 + z.im^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Actual normalized two-dimensional Gaussian generating integral. The two
linear complex coefficients are independent; no reality hypothesis is used. -/
theorem complex_gaussian_generating (a b : ℂ) :
    (∫ z : ℂ, Complex.exp (-(‖z‖^2 : ℂ) + a*z + b*conj z)) =
      (Real.pi : ℂ) * Complex.exp (a*b) := by
  let coeff : Fin 2 → ℂ := ![a+b, Complex.I*(a-b)]
  have h := GaussianFourier.integral_cexp_neg_mul_sum_add (ι := Fin 2) (b := (1 : ℂ))
    (by norm_num : 0 < (1 : ℂ).re) coeff
  rw [← Complex.volume_preserving_equiv_pi.symm.integral_comp
    Complex.measurableEquivPi.symm.measurableEmbedding]
  calc
    _ = ∫ v : Fin 2 → ℝ, Complex.exp (-(1 : ℂ) * ∑ i : Fin 2, (v i : ℂ)^2 +
        ∑ i : Fin 2, coeff i * (v i : ℂ)) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro v
      change Complex.exp (-(‖Complex.measurableEquivPi.symm v‖^2 : ℂ) +
        a * Complex.measurableEquivPi.symm v + b * conj (Complex.measurableEquivPi.symm v)) =
        Complex.exp (-(1 : ℂ) * ∑ i : Fin 2, (v i : ℂ)^2 +
          ∑ i : Fin 2, coeff i * (v i : ℂ))
      congr 1
      simp only [← Complex.ofReal_pow]
      rw [norm_sq_real_coords]
      simp [Complex.measurableEquivPi_symm_apply, coeff, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_add, Complex.ofReal_pow, map_add, map_mul]
      ring
    _ = _ := by
      rw [h]
      simp only [coeff, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fintype.card_fin]
      have hexp : ((a+b)^2 + (Complex.I*(a-b))^2) / (4 : ℂ) = a*b := by
        rw [mul_pow, Complex.I_sq]
        ring
      simp only [mul_one, div_one]
      rw [hexp]
      norm_num

theorem gaussianFactor_conj (k : ℝ) (z : ℂ) : conj (gaussianFactor k z) = gaussianFactor k z := by
  rw [gaussianFactor_eq_norm, ← Complex.exp_conj, Complex.conj_ofReal]

/-- The actual diagonal integrand after cancellation of the original phase.
The Laguerre formula is not used in this algebraic identity. -/
theorem planeJet_displacement_integrand (j : ℕ) (lambda z : ℂ) :
    conj (planeJet j z) * magneticTranslate 1 lambda (planeJet j) z =
      (Real.exp (-‖lambda‖^2 / 2) : ℂ) /
        (j.factorial : ℂ) *
      (Complex.exp (-(‖z‖^2 : ℂ) + z*conj lambda) *
        conj z^j * (z-lambda)^j) := by
  have hf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hs : ((Real.sqrt (j.factorial : ℝ) : ℂ))^2 = (j.factorial : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have htranslate : Complex.exp (magneticExponent 1 z lambda) * gaussianFactor 1 (z-lambda) =
      gaussianFactor 1 z * Complex.exp (z*conj lambda - (‖lambda‖^2 : ℂ)/2) := by
    unfold gaussianFactor
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have h := gaussian_translate_exponents 1 z lambda
    simpa only [Complex.ofReal_one, one_mul, Complex.mul_conj'] using h
  have ht : magneticTranslate 1 lambda (planeJet j) z =
      gaussianFactor 1 z * Complex.exp (z*conj lambda-(‖lambda‖^2 : ℂ)/2) *
        (z-lambda)^j / (Real.sqrt (j.factorial : ℝ) : ℂ) := by
    unfold magneticTranslate planeJet
    calc
      _ = (Complex.exp (magneticExponent 1 z lambda) * gaussianFactor 1 (z-lambda)) *
          (z-lambda)^j / (Real.sqrt (j.factorial : ℝ) : ℂ) := by ring
      _ = _ := by rw [htranslate]
  have hsquare : gaussianFactor 1 z * gaussianFactor 1 z = Complex.exp (-(‖z‖^2 : ℂ)) := by
    unfold gaussianFactor
    rw [← Complex.exp_add, Complex.mul_conj']
    congr 1
    norm_num
  have hproduct : gaussianFactor 1 z * gaussianFactor 1 z *
      Complex.exp (z*conj lambda-(‖lambda‖^2 : ℂ)/2) =
      (Real.exp (-‖lambda‖^2/2) : ℂ) * Complex.exp (-(‖z‖^2 : ℂ)+z*conj lambda) := by
    rw [hsquare, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [ht]
  simp only [planeJet, map_div₀, map_mul, map_pow, gaussianFactor_conj, Complex.conj_ofReal]
  calc
    _ = (gaussianFactor 1 z * gaussianFactor 1 z *
        Complex.exp (z*conj lambda-(‖lambda‖^2 : ℂ)/2)) *
        (conj z^j * (z-lambda)^j) / ((Real.sqrt (j.factorial : ℝ) : ℂ)^2) := by
          ring
    _ = _ := by rw [hproduct, hs]; ring

/-- Ground-state diagonal identity, with the original magnetic convention. -/
theorem planeJet_zero_displacement (lambda : ℂ) :
    planeInner (planeJet 0) (magneticTranslate 1 lambda (planeJet 0)) =
      (Real.exp (-‖lambda‖^2 / 2) : ℂ) := by
  unfold planeInner planeMeasure
  simp_rw [planeJet_displacement_integrand]
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
  rw [integral_smul_measure, integral_const_mul]
  have h := complex_gaussian_generating (conj lambda) 0
  simp only [zero_mul, mul_zero, add_zero, Complex.exp_zero, mul_one] at h
  simp_rw [mul_comm (conj lambda)] at h
  rw [h]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem paperLaguerre_zero (t : ℝ) : JetEnvelope.paperLaguerre 0 t = 1 := by
  simp [JetEnvelope.paperLaguerre]

theorem paperLaguerre_at_zero (j : ℕ) : JetEnvelope.paperLaguerre j 0 = 1 := by
  unfold JetEnvelope.paperLaguerre
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    simp [zero_pow hb0]
  · simp

theorem planeJet_groundstate_laguerre (lambda : ℂ) :
    planeInner (planeJet 0) (magneticTranslate 1 lambda (planeJet 0)) =
      ((Real.exp (-‖lambda‖^2 / 2) *
        JetEnvelope.paperLaguerre 0 (‖lambda‖^2) : ℝ) : ℂ) := by
  rw [paperLaguerre_zero, mul_one, planeJet_zero_displacement]

theorem planeJet_zero_shift_laguerre (j : ℕ) :
    planeInner (planeJet j) (magneticTranslate 1 0 (planeJet j)) =
      ((Real.exp (-‖(0 : ℂ)‖^2 / 2) *
        JetEnvelope.paperLaguerre j (‖(0 : ℂ)‖^2) : ℝ) : ℂ) := by
  rw [magneticTranslate_zero, planeJet_inner_self]
  simp [paperLaguerre_at_zero]

/-- The finite Leibniz calculation for the actual holomorphic displacement
factor. This is scalar polynomial calculus, separate from the integral. -/
theorem displacement_factor_derivative (j : ℕ) (lambda : ℂ) :
    iteratedDeriv j (fun z : ℂ => (z-lambda)^j * Complex.exp (conj lambda*z)) 0 =
      (j.factorial : ℂ) * (JetEnvelope.paperLaguerre j (‖lambda‖^2) : ℂ) := by
  have hd := iteratedDeriv_fun_mul (n := j) (x := (0 : ℂ))
    (f := fun z : ℂ => (z-lambda)^j)
    (g := fun z : ℂ => Complex.exp (conj lambda*z)) (by fun_prop) (by fun_prop)
  rw [hd]
  have hpd (n : ℕ) : iteratedDeriv n (fun z : ℂ => (z-lambda)^j) 0 =
      (j.descFactorial n : ℂ)*(-lambda)^(j-n) := by
    have h := congrFun (iteratedDeriv_comp_sub_const (n := n)
      (f := fun z : ℂ => z^j) (s := lambda)) 0
    simpa only [zero_sub, iteratedDeriv_pow] using h
  simp_rw [hpd, iteratedDeriv_cexp_const_mul]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  rw [← Finset.sum_range_reflect]
  unfold JetEnvelope.paperLaguerre
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrj : r ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  simp only [Nat.sub_sub_self hrj, Nat.choose_symm hrj]
  have hf : (r.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  have hfac : (r.factorial : ℂ) * (j.descFactorial (j-r) : ℂ) = (j.factorial : ℂ) := by
    norm_cast
    simpa only [Nat.sub_sub_self hrj] using
      (Nat.factorial_mul_descFactorial (Nat.sub_le j r))
  have hpow : (-lambda)^r * conj lambda^r = (-1 : ℂ)^r * (‖lambda‖^2 : ℂ)^r := by
    rw [neg_eq_neg_one_mul, mul_pow, mul_assoc, ← mul_pow lambda,
      Complex.mul_conj']
  calc
    _ = (j.choose r : ℂ)*(j.descFactorial (j-r) : ℂ)*
        ((-lambda)^r*conj lambda^r) := by ring
    _ = _ := by
      rw [hpow]
      field_simp
      rw [← hfac]
      ring

/-- Integrability of the actual mixed Gaussian-polynomial kernel is derived
from the canonical L2 product, rather than assumed as the diagonal identity. -/
theorem displacement_kernel_integrable (j : ℕ) (lambda : ℂ) :
    Integrable (fun z : ℂ => Complex.exp (-(‖z‖^2 : ℂ)+z*conj lambda)*
      conj z^j*(z-lambda)^j) := by
  have hp := planeInner_integrable (planeJet j) (magneticTranslate 1 lambda (planeJet j))
    (planeJet_memLp j) (magnetic_memLp 1 lambda (planeJet j) (planeJet_memLp j))
  have hs : Integrable (fun z : ℂ =>
      ((Real.exp (-‖lambda‖^2/2) : ℂ)/(j.factorial : ℂ)) *
      (Complex.exp (-(‖z‖^2 : ℂ)+z*conj lambda)*conj z^j*(z-lambda)^j)) planeMeasure := by
    apply hp.congr
    exact Filter.Eventually.of_forall (planeJet_displacement_integrand j lambda)
  have hcoeff : ((Real.exp (-‖lambda‖^2/2) : ℂ)/(j.factorial : ℂ)) ≠ 0 := by
    apply div_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    · exact Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hk := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hcoeff) _).mp hs
  rw [planeMeasure] at hk
  exact (integrable_smul_measure (by positivity) (by simp)).mp hk

/-- Mixed Gaussian moment obtained on the actual kernel's proved domain. -/
theorem displacement_kernel_integral (j : ℕ) (lambda : ℂ) :
    (∫ z : ℂ, Complex.exp (-(‖z‖^2 : ℂ)+z*conj lambda)*conj z^j*(z-lambda)^j) =
      (Real.pi : ℂ)*(j.factorial : ℂ)*
        (JetEnvelope.paperLaguerre j (‖lambda‖^2) : ℂ) := by
  have heq : (fun z : ℂ => Complex.exp (-(‖z‖^2 : ℂ)+z*conj lambda)*
      conj z^j*(z-lambda)^j) =
      (fun z : ℂ => Complex.exp (-(‖z‖^2 : ℂ))*conj z^j*
        ((z-lambda)^j*Complex.exp (conj lambda*z))) := by
    funext z
    rw [Complex.exp_add, mul_comm z (conj lambda)]
    ring
  have hk := displacement_kernel_integrable j lambda
  rw [heq] at hk ⊢
  rw [PlaneGaussianReproducing.gaussian_reproducing_derivative j _ (by fun_prop) hk,
    displacement_factor_derivative]
  ring

/-- Actual canonical diagonal identity, for all natural j and complex lambda.
All Gaussian, normalization and integrability obligations are derived. -/
theorem planeJet_displacement_laguerre (j : ℕ) (lambda : ℂ) :
    planeInner (planeJet j) (magneticTranslate 1 lambda (planeJet j)) =
      ((Real.exp (-‖lambda‖^2 / 2) *
        JetEnvelope.paperLaguerre j (‖lambda‖^2) : ℝ) : ℂ) := by
  unfold planeInner planeMeasure
  simp_rw [planeJet_displacement_integrand]
  rw [integral_smul_measure, integral_const_mul, displacement_kernel_integral,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  field_simp

theorem laguerre_displacement_modulus (j : ℕ) (lambda : ℂ) :
    Real.exp (-‖lambda‖^2/2)*|JetEnvelope.paperLaguerre j (‖lambda‖^2)| ≤ 1 := by
  have h := planeJet_displacement_modulus j lambda
  rw [planeJet_displacement_laguerre] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)] using h

/-- The scalar inner-region estimate now has no displacement identity premise. -/
theorem laguerre_modulus (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t/2)*|JetEnvelope.paperLaguerre j t| ≤ 1 := by
  have h := laguerre_displacement_modulus j (Real.sqrt t : ℂ)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t),
    Real.sq_sqrt ht] using h

end
end TorusLean.Fermion.PlaneJetDisplacement
