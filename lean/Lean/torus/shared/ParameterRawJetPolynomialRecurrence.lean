import torus.shared.ParameterRawJetLadderBasic
import Mathlib.Data.Nat.Choose.Sum

/-! Pure finite algebra of the already fixed raw-jet polynomial. This file
changes neither Gaussian nor factorial normalization and contains no integral,
Wirtinger identity, or energy inequality. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterRawJetLadder
open scoped ComplexConjugate BigOperators

/-- Pascal's identity, with the derivative iterates shifted on the right.
No regularity hypothesis is needed for this purely algebraic recurrence. -/
theorem jetPolynomial_succ (F : ℂ → ℂ) (j : ℕ) (R : ℂ) :
    jetPolynomial F (j+1) R =
      (-conj R) * jetPolynomial F j R + jetPolynomial (deriv F) j R := by
  have hp := Finset.sum_choose_succ_mul
    (fun n k => iteratedDeriv n F R * (-conj R)^k) j
  calc
    jetPolynomial F (j+1) R =
        (∑ n ∈ Finset.range (j+1), (j.choose n : ℂ) *
          iteratedDeriv n F R * (-conj R)^(j+1-n)) +
        ∑ n ∈ Finset.range (j+1), (j.choose n : ℂ) *
          iteratedDeriv (n+1) F R * (-conj R)^(j-n) := by
      simpa only [jetPolynomial, Nat.add_assoc, mul_assoc] using hp
    _ = (-conj R) * jetPolynomial F j R + jetPolynomial (deriv F) j R := by
      congr 1
      · rw [jetPolynomial, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        have hnle : n ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
        have he : j+1-n = j-n+1 := by omega
        rw [he, pow_succ]
        ring
      · simp only [jetPolynomial, iteratedDeriv_succ']

/-- Natural subtraction is retained. The identity remains true for n>j+1
because the binomial coefficients vanish; no implicit subtraction domain. -/
theorem choose_succ_mul_sub (j n : ℕ) :
    (j+1).choose n * (j+1-n) = (j+1) * j.choose n := by
  rw [← Nat.choose_mul_succ_eq, Nat.mul_comm]

theorem choose_succ_mul_sub_complex (j n : ℕ) :
    ((j+1).choose n : ℂ) * ((j+1-n : ℕ) : ℂ) =
      ((j+1 : ℕ) : ℂ) * (j.choose n : ℂ) := by
  exact_mod_cast choose_succ_mul_sub j n

/-- General finite binomial lowering sum, for an arbitrary coefficient
sequence. The endpoint n=j+1 vanishes before any exponent manipulation. -/
theorem sum_choose_succ_mul_sub (a : ℕ → ℂ) (t : ℂ) (j : ℕ) :
    (∑ n ∈ Finset.range (j+2), ((j+1).choose n : ℂ) *
      ((j+1-n : ℕ) : ℂ) * a n * t^(j-n)) =
      ((j+1 : ℕ) : ℂ) *
        ∑ n ∈ Finset.range (j+1), (j.choose n : ℂ) * a n * t^(j-n) := by
  rw [show j+2 = (j+1)+1 by omega, Finset.sum_range_succ]
  simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [choose_succ_mul_sub_complex]
  ring

/-- The finite coefficient identity needed by the anti-holomorphic ladder. -/
theorem jetPolynomial_weighted_succ (F : ℂ → ℂ) (j : ℕ) (R : ℂ) :
    (∑ n ∈ Finset.range (j+2), ((j+1).choose n : ℂ) *
      ((j+1-n : ℕ) : ℂ) * iteratedDeriv n F R * (-conj R)^(j-n)) =
      ((j+1 : ℕ) : ℂ) * jetPolynomial F j R := by
  exact sum_choose_succ_mul_sub (fun n => iteratedDeriv n F R) (-conj R) j

/-- Version in the literal exponent produced when differentiating a power. -/
theorem jetPolynomial_weighted_succ_power (F : ℂ → ℂ) (j : ℕ) (R : ℂ) :
    (∑ n ∈ Finset.range (j+2), ((j+1).choose n : ℂ) *
      ((j+1-n : ℕ) : ℂ) * iteratedDeriv n F R * (-conj R)^(j+1-n-1)) =
      ((j+1 : ℕ) : ℂ) * jetPolynomial F j R := by
  have he : ∀ n : ℕ, j+1-n-1 = j-n := by intro n; omega
  simp_rw [he]
  exact jetPolynomial_weighted_succ F j R

#print axioms jetPolynomial_succ
#print axioms choose_succ_mul_sub
#print axioms sum_choose_succ_mul_sub
#print axioms jetPolynomial_weighted_succ
#print axioms jetPolynomial_weighted_succ_power
end TorusLean.Shared.ParameterRawJetLadder
