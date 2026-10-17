import torus.shared.ThermalCoherentMoments
import Mathlib.Analysis.SpecificLimits.Normed

/-! Scalar thermal-binomial weights for the normalized three-body Jacobi
change of variables. This file proves actual summability and its exact value.
It does not identify an Omega, center-of-mass, or partial-trace operator. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiWeights
open TorusLean.Shared.ThermalCoherentMoments

/-- The exact real coefficient obtained by normalizing both the relative
seed and its center-of-mass descendant. All factorials are ordinary natural
factorials coerced to the reals. -/
def jacobiAmplitude (n d : ℕ) : ℝ :=
  ((n+d).choose d : ℝ) * Real.sqrt ((6 : ℝ)^d * (d.factorial : ℝ)) *
    Real.sqrt ((3 : ℝ)^n * (n.factorial : ℝ)) /
      ((3 : ℝ)^(n+d) * Real.sqrt ((n+d).factorial : ℝ))

theorem jacobiAmplitude_nonneg (n d : ℕ) : 0 ≤ jacobiAmplitude n d := by
  unfold jacobiAmplitude
  positivity

/-- Exact square of the normalization coefficient, without floating-point
constants or any assumption on the degrees. -/
theorem jacobiAmplitude_sq (n d : ℕ) :
    (jacobiAmplitude n d)^2 =
      ((n+d).choose d : ℝ) * (1/3 : ℝ)^n * (2/3 : ℝ)^d := by
  have hf : ((n+d).choose d : ℝ) * (d.factorial : ℝ) * (n.factorial : ℝ) =
      ((n+d).factorial : ℝ) := by
    have hn := Nat.add_choose_mul_factorial_mul_factorial n d
    have hc : ((n+d).choose d : ℝ) * (n.factorial : ℝ) * (d.factorial : ℝ) =
        ((n+d).factorial : ℝ) := by exact_mod_cast hn
    simpa only [mul_right_comm] using hc
  have hnum : ((n+d).choose d : ℝ)^2 * ((6 : ℝ)^d * (d.factorial : ℝ)) *
      ((3 : ℝ)^n * (n.factorial : ℝ)) =
        ((n+d).choose d : ℝ) * ((n+d).factorial : ℝ) *
          ((2 : ℝ)^d * (3 : ℝ)^(n+d)) := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, mul_pow, pow_add]
    calc
      _ = (((n+d).choose d : ℝ) * (d.factorial : ℝ) * (n.factorial : ℝ)) *
          ((n+d).choose d : ℝ) * (2 : ℝ)^d * (3 : ℝ)^d * (3 : ℝ)^n := by ring
      _ = _ := by rw [hf]; ring
  have hthree : (3 : ℝ)^(n+d) ≠ 0 := by positivity
  have hfact : ((n+d).factorial : ℝ) ≠ 0 := by positivity
  unfold jacobiAmplitude
  rw [div_pow, mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ (6 : ℝ)^d * (d.factorial : ℝ)),
    Real.sq_sqrt (by positivity : 0 ≤ (3 : ℝ)^n * (n.factorial : ℝ)),
    Real.sq_sqrt (by positivity : 0 ≤ ((n+d).factorial : ℝ)), hnum]
  calc
    _ = ((n+d).choose d : ℝ) * ((2 : ℝ)^d / (3 : ℝ)^(n+d)) := by
      field_simp [hthree, hfact]
    _ = _ := by
      simp only [div_eq_mul_inv, pow_add, mul_pow, mul_inv, inv_pow, one_pow]
      ring

/-- Thermal occupation weight at spectator degree `n` and relative degree `d`.
The leading `2/3` is the measure/center-of-mass partial-trace prefactor.
The remaining binomial and power factors are the Jacobi amplitude square. -/
def thermalJacobiWeight (a : ℝ) (d n : ℕ) : ℝ :=
  (2/3 : ℝ) * thermalEigenvalue a (n+d) * ((n+d).choose d : ℝ) *
    (1/3 : ℝ)^n * (2/3 : ℝ)^d

theorem thermalJacobiWeight_nonneg (a : ℝ) (ha : 0 < a) (d n : ℕ) :
    0 ≤ thermalJacobiWeight a d n := by
  unfold thermalJacobiWeight
  have hthermal := (thermalEigenvalue_pos a ha (n+d)).le
  positivity

/-- The thermal weight is exactly the thermal eigenvalue times the square
of the normalized Jacobi amplitude, including the prefactor `2/3`. -/
theorem thermalJacobiWeight_eq_amplitude_sq (a : ℝ) (d n : ℕ) :
    thermalJacobiWeight a d n =
      (2/3 : ℝ) * thermalEigenvalue a (n+d) * (jacobiAmplitude n d)^2 := by
  rw [jacobiAmplitude_sq]
  unfold thermalJacobiWeight
  ring

/-- Exact factorization into a constant and the standard binomial series. -/
theorem thermalJacobiWeight_eq_geometric (a : ℝ) (d n : ℕ) :
    thermalJacobiWeight a d n =
      (2 / (3 * (1+a)))^(d+1) *
        (((n+d).choose d : ℝ) * (1 / (3 * (1+a)))^n) := by
  simp only [thermalJacobiWeight, thermalEigenvalue, div_eq_mul_inv,
    mul_pow, pow_add, pow_succ, mul_inv, inv_pow, one_pow]
  ring

/-- The full infinite Jacobi weight sum exists for every positive thermal
parameter, with no summability assumption supplied by the caller. -/
theorem hasSum_thermalJacobiWeight (a : ℝ) (ha : 0 < a) (d : ℕ) :
    HasSum (thermalJacobiWeight a d) ((2 / (2 + 3*a))^(d+1)) := by
  have hden : 0 < 3 * (1+a) := by positivity
  have hratio : (1 : ℝ) / (3 * (1+a)) < 1 :=
    (div_lt_one hden).2 (by linarith)
  have hnorm : ‖(1 : ℝ) / (3 * (1+a))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hden)]
    exact hratio
  have hquot : (2 / (3 * (1+a))) / (1 - (1 : ℝ) / (3 * (1+a))) =
      2 / (2 + 3*a) := by
    rw [one_sub_div hden.ne', div_div_div_cancel_right₀ hden.ne',
      show 3 * (1+a) - 1 = 2 + 3*a by ring]
  have hvalue : (2 / (3 * (1+a)))^(d+1) *
      (1 / (1 - (1 : ℝ) / (3 * (1+a)))^(d+1)) =
        (2 / (2 + 3*a))^(d+1) := by
    rw [mul_one_div, ← div_pow, hquot]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one d hnorm).mul_left
    ((2 / (3 * (1+a)))^(d+1))
  rw [hvalue] at h
  convert h using 1
  funext n
  exact thermalJacobiWeight_eq_geometric a d n

theorem summable_thermalJacobiWeight (a : ℝ) (ha : 0 < a) (d : ℕ) :
    Summable (thermalJacobiWeight a d) :=
  (hasSum_thermalJacobiWeight a ha d).summable

theorem tsum_thermalJacobiWeight (a : ℝ) (ha : 0 < a) (d : ℕ) :
    ∑' n, thermalJacobiWeight a d n = (2 / (2 + 3*a))^(d+1) :=
  (hasSum_thermalJacobiWeight a ha d).tsum_eq

/-- Expanded version exposing the frozen thermal eigenvalues and the exact
binomial factors directly. -/
theorem hasSum_thermal_binomial (a : ℝ) (ha : 0 < a) (d : ℕ) :
    HasSum (fun n : ℕ =>
      (2/3 : ℝ) * thermalEigenvalue a (n+d) * ((n+d).choose d : ℝ) *
        (1/3 : ℝ)^n * (2/3 : ℝ)^d)
      ((2 / (2 + 3*a))^(d+1)) :=
  hasSum_thermalJacobiWeight a ha d

/-- The same convergent sum written directly in the normalized amplitudes. -/
theorem hasSum_thermal_amplitude_sq (a : ℝ) (ha : 0 < a) (d : ℕ) :
    HasSum (fun n : ℕ =>
      (2/3 : ℝ) * thermalEigenvalue a (n+d) * (jacobiAmplitude n d)^2)
      ((2 / (2 + 3*a))^(d+1)) := by
  simpa only [← thermalJacobiWeight_eq_amplitude_sq] using
    hasSum_thermalJacobiWeight a ha d

end TorusLean.Shared.ThermalCoherentJacobiWeights
