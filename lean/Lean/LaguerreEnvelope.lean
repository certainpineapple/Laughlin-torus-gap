import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual finite Laguerre estimate used in paper `lem:jets`.
This is the outer-region analytic substep, not the torus inner-unfold formula
or the complete uniform raw-jet norm bound. No physical model is redefined. -/

set_option autoImplicit false

namespace TorusLean.Fermion.JetEnvelope

open scoped BigOperators

/-- Ordinary Laguerre polynomial L_j(t), with the manuscript's j and t=|lambda|².
This scalar finite series is not a physical jet or a torus inner product. -/
noncomputable def paperLaguerre (j : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (j + 1),
    (-1 : ℝ) ^ r * (j.choose r : ℝ) * t ^ r / (r.factorial : ℝ)

private theorem laguerre_term_abs_le (j r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |(-1 : ℝ) ^ r * (j.choose r : ℝ) * t ^ r / (r.factorial : ℝ)| ≤
      ((j : ℝ) * t) ^ r / (r.factorial : ℝ) ^ 2 := by
  have hf : (0 : ℝ) ≤ (r.factorial : ℝ) := Nat.cast_nonneg _
  have hc : (j.choose r : ℝ) ≤ (j : ℝ) ^ r / (r.factorial : ℝ) := by
    exact Nat.choose_le_pow_div r j
  calc
    _ = (j.choose r : ℝ) * t ^ r / (r.factorial : ℝ) := by
      simp [abs_mul, abs_div, abs_pow, abs_of_nonneg ht]
    _ ≤ (((j : ℝ) ^ r / (r.factorial : ℝ)) * t ^ r) /
        (r.factorial : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (pow_nonneg ht r)) hf
    _ = _ := by rw [mul_pow]; ring

theorem laguerre_abs_le_factorial_sum (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |paperLaguerre j t| ≤
      ∑ r ∈ Finset.range (j + 1), ((j : ℝ) * t) ^ r / (r.factorial : ℝ) ^ 2 := by
  unfold paperLaguerre
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun r hr => laguerre_term_abs_le j r t ht)

theorem laguerre_abs_le_exp (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |paperLaguerre j t| ≤ Real.exp (2 * Real.sqrt ((j : ℝ) * t)) := by
  have hprod : 0 ≤ (j : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht
  have heq (r : ℕ) :
      ((j : ℝ) * t) ^ r / (r.factorial : ℝ) ^ 2 =
        (Real.sqrt ((j : ℝ) * t) ^ r / (r.factorial : ℝ)) ^ 2 := by
    rw [div_pow, ← pow_mul, Nat.mul_comm r 2, pow_mul, Real.sq_sqrt hprod]
  have hnonneg (r : ℕ) (_ : r ∈ Finset.range (j + 1)) :
      0 ≤ Real.sqrt ((j : ℝ) * t) ^ r / (r.factorial : ℝ) := by
    exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ r ∈ Finset.range (j + 1),
        ((j : ℝ) * t) ^ r / (r.factorial : ℝ) ^ 2 :=
      laguerre_abs_le_factorial_sum j t ht
    _ = ∑ r ∈ Finset.range (j + 1),
        (Real.sqrt ((j : ℝ) * t) ^ r / (r.factorial : ℝ)) ^ 2 := by
      exact Finset.sum_congr rfl (fun r hr => heq r)
    _ ≤ (∑ r ∈ Finset.range (j + 1),
        Real.sqrt ((j : ℝ) * t) ^ r / (r.factorial : ℝ)) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg hnonneg
    _ ≤ Real.exp (Real.sqrt ((j : ℝ) * t)) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg hnonneg)
        (Real.sum_le_exp_of_nonneg (Real.sqrt_nonneg _) (j + 1)) 2
    _ = _ := by rw [← Real.exp_nat_mul]; norm_num

/-- The paper's t >= 64j outer-region estimate, including j=0 and t=0.
There is no envelope, lattice counting or torus norm hypothesis. -/
theorem laguerre_gaussian_far_bound (j : ℕ) (t : ℝ)
    (hfar : 64 * (j : ℝ) ≤ t) :
    Real.exp (-t / 2) * |paperLaguerre j t| ≤ Real.exp (-t / 4) := by
  have ht : 0 ≤ t := le_trans (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hfar
  have hs : Real.sqrt ((j : ℝ) * t) ≤ t / 8 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact div_nonneg ht (by norm_num)
    · nlinarith [mul_nonneg ht (sub_nonneg.mpr hfar)]
  calc
    _ ≤ Real.exp (-t / 2) * Real.exp (2 * Real.sqrt ((j : ℝ) * t)) :=
      mul_le_mul_of_nonneg_left (laguerre_abs_le_exp j t ht) (Real.exp_nonneg _)
    _ = Real.exp (-t / 2 + 2 * Real.sqrt ((j : ℝ) * t)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem laguerre_displacement_factor_far_bound (j : ℕ) (t : ℝ)
    (hfar : 64 * (j : ℝ) ≤ t) :
    |Real.exp (-t / 2) * paperLaguerre j t| ≤ Real.exp (-t / 4) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact laguerre_gaussian_far_bound j t hfar

end TorusLean.Fermion.JetEnvelope
