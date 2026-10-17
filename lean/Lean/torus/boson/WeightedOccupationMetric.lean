import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Actual finite-mode occupation weights on the polynomial core

There is no occupation cutoff. The finite mode set is an abstract coordinate
set, not a definition or a proved dimension of the physical torus LLL.
`scale i = 1` gives the canonical Bargmann occupation weight. The paper's
rational coordinates use `scale j = j!`, giving `∏ n_j! (j!)^n_j`.

The exact one-step weight identity is the normalization needed for
`(∂i)* = xi / scale i`. Full inner-product adjointness and its unitary bridge
to the physical torus symmetric Fock space are still pending.
-/

namespace TorusLean.Boson

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable section

def occupationMetricWeight (scale : ι → ℕ) (n : ι →₀ ℕ) : ℕ :=
  ∏ i, (n i).factorial * scale i ^ n i

theorem occupationMetricWeight_pos (scale : ι → ℕ)
    (hscale : ∀ i, 0 < scale i) (n : ι →₀ ℕ) :
    0 < occupationMetricWeight scale n := by
  unfold occupationMetricWeight
  exact Finset.prod_pos fun i _ =>
    Nat.mul_pos (Nat.factorial_pos _) (pow_pos (hscale i) _)

theorem occupationMetricWeight_add_single (scale : ι → ℕ)
    (n : ι →₀ ℕ) (i : ι) :
    occupationMetricWeight scale (n + Finsupp.single i 1) =
      (n i + 1) * scale i * occupationMetricWeight scale n := by
  classical
  let f : ι → ℕ := fun j => (n j).factorial * scale j ^ n j
  let g : ι → ℕ := fun j =>
    ((n + Finsupp.single i 1 : ι →₀ ℕ) j).factorial *
      scale j ^ ((n + Finsupp.single i 1 : ι →₀ ℕ) j)
  have heq : (∏ j ∈ Finset.univ.erase i, g j) =
      ∏ j ∈ Finset.univ.erase i, f j := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [g, f, Finsupp.add_apply, Finsupp.single_apply, hji, Ne.symm hji]
  change (∏ j, g j) = (n i + 1) * scale i * ∏ j, f j
  rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i), heq]
  simp only [g, f, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorial_succ, pow_succ]
  ring

/-- A genuine weighted squared norm expression for every finite polynomial. -/
def occupationMetricNormSq (scale : ι → ℕ) (f : MvPolynomial ι ℂ) : ℝ :=
  ∑ n ∈ f.support, (occupationMetricWeight scale n : ℝ) * Complex.normSq (f.coeff n)

theorem occupationMetricNormSq_nonneg (scale : ι → ℕ) (f : MvPolynomial ι ℂ) :
    0 ≤ occupationMetricNormSq scale f := by
  unfold occupationMetricNormSq
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

theorem occupationMetricNormSq_monomial (scale : ι → ℕ) (n : ι →₀ ℕ) (c : ℂ) :
    occupationMetricNormSq scale (MvPolynomial.monomial n c) =
      (occupationMetricWeight scale n : ℝ) * Complex.normSq c := by
  classical
  by_cases hc : c = 0
  · subst c
    simp [occupationMetricNormSq]
  · simp [occupationMetricNormSq, MvPolynomial.support_monomial, hc]

#print axioms occupationMetricWeight_pos
#print axioms occupationMetricWeight_add_single
#print axioms occupationMetricNormSq_nonneg
#print axioms occupationMetricNormSq_monomial

end

end TorusLean.Boson
