import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The real coefficients in paper eq:F-Dz, without any normalization input.
The half powers are written as natural powers of positive square roots. -/

set_option autoImplicit false

namespace TorusLean.Fermion

open scoped BigOperators

noncomputable def paperPauliCoefficient (z p : ℕ) : ℝ :=
  (-1) ^ (z - p) * Real.sqrt (Nat.choose z p : ℝ) *
    Real.sqrt (1 / 3 : ℝ) ^ p * Real.sqrt (2 / 3 : ℝ) ^ (z - p)

theorem paperPauliCoefficient_sq (z p : ℕ) :
    paperPauliCoefficient z p ^ 2 =
      (Nat.choose z p : ℝ) * (1 / 3 : ℝ) ^ p * (2 / 3 : ℝ) ^ (z - p) := by
  unfold paperPauliCoefficient
  have hp : ∀ (a : ℝ) (n : ℕ), (a ^ n) ^ 2 = (a ^ 2) ^ n := by
    intro a n
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  simp only [mul_pow]
  rw [hp (-1) (z - p), hp (Real.sqrt (1 / 3 : ℝ)) p,
    hp (Real.sqrt (2 / 3 : ℝ)) (z - p)]
  rw [Real.sq_sqrt (Nat.cast_nonneg (Nat.choose z p)),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  norm_num

theorem paperPauliCoefficient_sq_sum (z : ℕ) :
    (∑ p : Fin (z + 1), paperPauliCoefficient z p.val ^ 2) = 1 := by
  simp_rw [paperPauliCoefficient_sq]
  rw [Fin.sum_univ_eq_sum_range (fun p : ℕ =>
    (Nat.choose z p : ℝ) * (1 / 3 : ℝ) ^ p * (2 / 3 : ℝ) ^ (z - p))]
  calc
    _ = ((1 / 3 : ℝ) + (2 / 3 : ℝ)) ^ z := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = 1 := by norm_num

end TorusLean.Fermion
