import PlaneMagneticUnitary
import torus.geometry.Periodization
import Mathlib.MeasureTheory.Integral.Gamma

/-! Actual canonical planeJet normalization in the existing d²z/pi model.
The jet, Gaussian and magnetic action are imported unchanged from geometry.
Radial Gaussian moments are reused from Mathlib, not assumed as model fields. -/

set_option autoImplicit false

namespace TorusLean.Fermion.CanonicalPlaneJets

open MeasureTheory TorusLean.Geometry PlaneMagneticUnitary
open scoped ComplexConjugate ENNReal

noncomputable section

theorem planeJet_continuous (j : ℕ) : Continuous (planeJet j) := by
  unfold planeJet gaussianFactor
  fun_prop

theorem gaussianFactor_one_norm (z : ℂ) :
    ‖gaussianFactor 1 z‖ = Real.exp (-‖z‖^2 / 2) := by
  rw [gaussianFactor_eq_norm, Complex.norm_exp]
  simp
  norm_cast

theorem planeJet_norm (j : ℕ) (z : ℂ) :
    ‖planeJet j z‖ = Real.exp (-‖z‖^2 / 2) * ‖z‖^j / Real.sqrt (j.factorial : ℝ) := by
  rw [planeJet, norm_div, norm_mul, norm_pow, gaussianFactor_one_norm]
  simp [Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem planeJet_norm_sq (j : ℕ) (z : ℂ) :
    ‖planeJet j z‖^2 = ‖z‖^(2*j) * Real.exp (-‖z‖^2) / (j.factorial : ℝ) := by
  rw [planeJet_norm, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have he : Real.exp (-‖z‖^2 / 2)^2 = Real.exp (-‖z‖^2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  congr 1
  rw [← pow_mul, Nat.mul_comm j 2, mul_comm]

/-- The exact plane Gaussian moment, in the canonical complex volume:
polar angular mass 2*pi and the radial p=2 factor give pi*j!. -/
theorem canonical_radial_moment (j : ℕ) :
    (∫ z : ℂ, ‖z‖^(2*j) * Real.exp (-‖z‖^2)) = Real.pi * (j.factorial : ℝ) := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((2*j : ℕ) : ℝ))
    (by norm_num) (by nlinarith [(Nat.cast_nonneg (2*j) : (0 : ℝ) ≤ (2*j : ℕ))])
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  have ha : (((2*j : ℕ) : ℝ) + 2) / 2 = (j : ℝ) + 1 := by push_cast; ring
  rw [ha, Real.Gamma_nat_eq_factorial] at h
  simpa using h

theorem canonical_radial_integrable (j : ℕ) :
    Integrable (fun z : ℂ => ‖z‖^(2*j) * Real.exp (-‖z‖^2)) volume := by
  apply Integrable.of_integral_ne_zero
  rw [canonical_radial_moment]
  exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr j.factorial_ne_zero)

private theorem norm_radial_integrable (j : ℕ) :
    Integrable (fun z : ℂ => ‖z‖^j * Real.exp (-‖z‖^2 / 2)) volume := by
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (j : ℝ))
    (b := 1/2) (by norm_num)
    (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) (by norm_num)
  have he : (fun z : ℂ => ‖z‖^j * Real.exp (-‖z‖^2 / 2)) =
      (fun z : ℂ => ‖z‖^(j : ℝ) * Real.exp (-(1/2) * ‖z‖^(2 : ℝ))) := by
    funext z
    rw [Real.rpow_natCast, Real.rpow_two]
    congr 2
    ring
  apply Integrable.of_integral_ne_zero
  rw [he, h]
  apply ne_of_gt
  apply mul_pos
  · apply mul_pos
    · norm_num [Real.pi_pos]
    · exact Real.rpow_pos_of_pos (by norm_num) _
  · apply Real.Gamma_pos_of_pos
    positivity

theorem planeJet_integrable (j : ℕ) : Integrable (planeJet j) planeMeasure := by
  have h := ((norm_radial_integrable j).div_const (Real.sqrt (j.factorial : ℝ))).smul_measure
    (c := ENNReal.ofReal (1 / Real.pi)) (by simp)
  apply h.mono' (planeJet_continuous j).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [planeJet_norm]
  apply le_of_eq
  ring

theorem planeJet_sq_integrable (j : ℕ) :
    Integrable (fun z : ℂ => ‖planeJet j z‖^2) planeMeasure := by
  have h := ((canonical_radial_integrable j).div_const (j.factorial : ℝ)).smul_measure
    (c := ENNReal.ofReal (1 / Real.pi)) (by simp)
  simpa only [planeMeasure, planeJet_norm_sq] using h

theorem planeJet_square_integral (j : ℕ) :
    (∫ z : ℂ, ‖planeJet j z‖^2 ∂planeMeasure) = 1 := by
  simp_rw [planeJet_norm_sq]
  rw [planeMeasure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / Real.pi)]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, canonical_radial_moment]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero, Nat.cast_ne_zero.mpr j.factorial_ne_zero]

theorem planeJet_memLp (j : ℕ) : MemLp (planeJet j) 2 planeMeasure :=
  (memLp_two_iff_integrable_sq_norm (planeJet_continuous j).aestronglyMeasurable).mpr
    (planeJet_sq_integrable j)

/-- Actual canonical oscillator normalization, with no normalization premise. -/
theorem planeJet_norm_toLp (j : ℕ) : ‖(planeJet_memLp j).toLp (planeJet j)‖ = 1 := by
  rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp) (planeJet_memLp j)]
  simp [planeJet_square_integral]

theorem planeJet_inner_self (j : ℕ) : planeInner (planeJet j) (planeJet j) = 1 := by
  rw [planeInner_eq_L2_inner _ _ (planeJet_memLp j) (planeJet_memLp j)]
  rw [inner_self_eq_norm_sq_to_K, planeJet_norm_toLp]
  norm_num

theorem translatedPlaneJet_memLp (j : ℕ) (R : ℂ) :
    MemLp (translatedPlaneJet j R) 2 planeMeasure :=
  magnetic_memLp 1 R (planeJet j) (planeJet_memLp j)

theorem translatedPlaneJet_norm_toLp (j : ℕ) (R : ℂ) :
    ‖(translatedPlaneJet_memLp j R).toLp (translatedPlaneJet j R)‖ = 1 := by
  change ‖(magnetic_memLp 1 R (planeJet j) (planeJet_memLp j)).toLp
    (magneticTranslate 1 R (planeJet j))‖ = 1
  rw [magnetic_norm_toLp 1 R (planeJet j) (planeJet_memLp j), planeJet_norm_toLp]

/-- Actual canonical planeJet displacement modulus, all j and lambda, with
the L2 domain and normalization now derived rather than assumed. -/
theorem planeJet_displacement_modulus (j : ℕ) (lambda : ℂ) :
    ‖planeInner (planeJet j) (magneticTranslate 1 lambda (planeJet j))‖ ≤ 1 :=
  normalized_displacement_modulus 1 lambda (planeJet j)
    (planeJet_memLp j) (planeJet_norm_toLp j)

theorem translatedPlaneJet_displacement_modulus (j : ℕ) (R lambda : ℂ) :
    ‖planeInner (translatedPlaneJet j R)
      (magneticTranslate 1 lambda (translatedPlaneJet j R))‖ ≤ 1 :=
  normalized_displacement_modulus 1 lambda (translatedPlaneJet j R)
    (translatedPlaneJet_memLp j R) (translatedPlaneJet_norm_toLp j R)

end
end TorusLean.Fermion.CanonicalPlaneJets
