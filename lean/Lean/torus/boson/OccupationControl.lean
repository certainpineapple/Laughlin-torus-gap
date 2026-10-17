import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite occupation estimates

These are discrete occupation and finite weighted-form statements. They are
independent of particle number. The required physical pair-form comparison
`(a(β)^2)†a(β)^2 / 2 ≤ c H` remains pending; no Hamiltonian is defined here.
-/

namespace TorusLean.Boson

open scoped BigOperators

/-- The two-particle factorial occupation for a nonnegative integral occupation. -/
noncomputable def pairOccupation (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) - 1) / 2

theorem occupation_le_pair_plus_one (n : ℕ) :
    (n : ℝ) ≤ pairOccupation n + 1 := by
  cases n with
  | zero => norm_num [pairOccupation]
  | succ n =>
    cases n with
    | zero => norm_num [pairOccupation]
    | succ n =>
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      simp only [pairOccupation, Nat.cast_succ]
      nlinarith [sq_nonneg (n : ℝ)]

theorem occupation_square_eq_pair (n : ℕ) :
    (n : ℝ) ^ 2 = 2 * pairOccupation n + (n : ℝ) := by
  unfold pairOccupation
  ring

/-- A finite occupation expansion with arbitrary nonnegative squared amplitudes. -/
theorem finite_occupation_le_pair_plus_mass {I : Type*} (s : Finset I)
    (occupation : I → ℕ) (weight : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weight i) :
    (∑ i ∈ s, weight i * (occupation i : ℝ)) ≤
      (∑ i ∈ s, weight i * pairOccupation (occupation i)) + ∑ i ∈ s, weight i := by
  have h := Finset.sum_le_sum (s := s) fun i hi =>
    mul_le_mul_of_nonneg_left (occupation_le_pair_plus_one (occupation i)) (hw i hi)
  simpa only [mul_add, mul_one, Finset.sum_add_distrib] using h

/-- Conditional form of the coherent estimate: the pair budget is an explicit input. -/
theorem finite_occupation_le_given_pair_budget {I : Type*} (s : Finset I)
    (occupation : I → ℕ) (weight : I → ℝ) (pairBudget : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weight i)
    (hpair : (∑ i ∈ s, weight i * pairOccupation (occupation i)) ≤ pairBudget) :
    (∑ i ∈ s, weight i * (occupation i : ℝ)) ≤ pairBudget + ∑ i ∈ s, weight i :=
  (finite_occupation_le_pair_plus_mass s occupation weight hw).trans
    (add_le_add hpair le_rfl)

#print axioms occupation_le_pair_plus_one
#print axioms occupation_square_eq_pair
#print axioms finite_occupation_le_pair_plus_mass
#print axioms finite_occupation_le_given_pair_budget

end TorusLean.Boson
