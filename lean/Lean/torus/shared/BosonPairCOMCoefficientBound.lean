import torus.shared.ThermalCoherentJacobiPair
import Mathlib.Data.Nat.Choose.Bounds

/-! Bounds for the literal ordered binomial coefficients of the original
pair-COM seed. No image is re-normalized after physical periodization. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonPairCOMCoefficientBound
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

/-- The real coefficient in the frozen pair-COM binomial expansion. -/
def pairCOMCoefficientReal (l i : ℕ) : ℝ :=
  (l.choose i : ℝ) * Real.sqrt (i.factorial : ℝ) *
    Real.sqrt ((l-i).factorial : ℝ) /
      (Real.sqrt ((2:ℝ)^l * (l.factorial:ℝ)) * Real.sqrt (2:ℝ))

/-- Exact squared coefficient, including coincident ordered labels. -/
theorem pairCOMCoefficientReal_sq (l i : ℕ) (hi : i ≤ l) :
    pairCOMCoefficientReal l i ^ 2 = (l.choose i : ℝ) / (2^(l+1):ℝ) := by
  have hf : (l.choose i : ℝ) * (i.factorial : ℝ) * ((l-i).factorial : ℝ) =
      (l.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hn : (l.factorial : ℝ) ≠ 0 := by positivity
  have hp : (2:ℝ)^l ≠ 0 := by positivity
  unfold pairCOMCoefficientReal
  rw [div_pow, mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ i.factorial),
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ (l-i).factorial),
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2^l*(l.factorial:ℝ)),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), pow_succ]
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero hp hn) (by norm_num))
    (mul_ne_zero hp (by norm_num))).mpr
  calc
    _ = ((l.choose i : ℝ) * (i.factorial : ℝ) * ((l-i).factorial : ℝ)) *
      ((l.choose i : ℝ) * ((2:ℝ)^l*2)) := by ring
    _ = _ := by rw [hf]; ring

/-- Uniform coefficient bound from choose(l,i) <= 2^l. -/
theorem pairCOMCoefficientReal_abs_le_one (l i : ℕ) (hi : i ≤ l) :
    |pairCOMCoefficientReal l i| ≤ 1 := by
  have hc : (l.choose i : ℝ) ≤ (2:ℝ)^l := by exact_mod_cast Nat.choose_le_two_pow l i
  have hs : pairCOMCoefficientReal l i ^ 2 ≤ (1:ℝ)/2 := by
    rw [pairCOMCoefficientReal_sq l i hi, pow_succ]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^l*2)).mpr
    nlinarith
  have ha := sq_abs (pairCOMCoefficientReal l i)
  nlinarith [abs_nonneg (pairCOMCoefficientReal l i)]

/-- At most l+1 in the literal ordered finite coefficient l1 budget. -/
theorem pairCOMCoefficientReal_sum_abs_le (l : ℕ) :
    (∑ i ∈ Finset.range (l+1), |pairCOMCoefficientReal l i|) ≤ (l:ℝ)+1 := by
  have h := Finset.sum_le_sum (s := Finset.range (l+1))
    (fun i hi => pairCOMCoefficientReal_abs_le_one l i (by have := Finset.mem_range.mp hi; omega))
  simpa using h

/-- The coefficient is literally the scalar in the old binomial source. -/
theorem pairCOMCoefficientReal_cast (l i : ℕ) :
    (pairCOMCoefficientReal l i : ℂ) =
      ((Real.sqrt ((2:ℝ)^l * (l.factorial:ℝ)) : ℂ)⁻¹ * (Real.sqrt (2:ℝ) : ℂ)⁻¹) *
        (l.choose i : ℂ) * (factorialRootNat i * factorialRootNat (l-i)) := by
  unfold pairCOMCoefficientReal factorialRootNat
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Same actual pair-COM polynomial with the bounded coefficients exposed. -/
theorem pairCOMSeed_eq_coefficient_sum (l : ℕ) :
    pairCOMSeed l = ∑ i ∈ Finset.range (l+1),
      (pairCOMCoefficientReal l i : ℂ) •
        ((MvPolynomial.X i : Core ℕ ℂ) * MvPolynomial.X (l-i)) := by
  rw [pairCOMSeed_binomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pairCOMCoefficientReal_cast, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]

#print axioms pairCOMCoefficientReal_sq
#print axioms pairCOMCoefficientReal_abs_le_one
#print axioms pairCOMCoefficientReal_sum_abs_le
#print axioms pairCOMCoefficientReal_cast
#print axioms pairCOMSeed_eq_coefficient_sum
end TorusLean.Shared.BosonPairCOMCoefficientBound
