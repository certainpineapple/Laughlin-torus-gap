import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! Exact scalar part of the manuscript's bosonic systole-twenty budget.
These statements do not assume or certify an all-N Hamiltonian inequality.
The lattice shell counting, mixed-jet estimate and relative-frame transfer
must be supplied separately by their physical definitions. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option exponentiation.threshold 1000
noncomputable section

namespace TorusLean.Shared.BosonSystole20Scalar
open scoped BigOperators

/-- Common allowance from section 5, including both diagonal kernel errors. -/
def allowance : ℝ := 1 / 100000000

def eta : ℝ := 764191703750823432978457 / 1500000000000000000000000

def rowCost : ℝ := 31171576329140678412829557 / 8750000000000000000000000

def delta : ℝ := 1 / 1000000

def c9 : ℝ := 30 * (5/9 : ℝ)^9

def c3 : ℝ := 12 * (9/8 : ℝ)^9

def c4 : ℝ := 272 * (9/8 : ℝ)^17

def alpha : ℝ := 1 - c9 - 1/50

def sAllowance : ℝ := 1 + allowance

def cAllowance : ℝ := (1 + allowance) / (1 - allowance)^2

def kappaAllowance : ℝ := 6 * rowCost * allowance

def budgetA (e2 s k : ℝ) : ℝ :=
  1 - e2 - eta - s * (c9 + (delta + k) * c3) - delta * c4 * s^2

def budgetB (e4 s c k : ℝ) : ℝ :=
  1 - alpha * (1 + e4) - s*c * (c9 + (delta + k) * c3) -
    2 * delta * c4 * s^2 * c

def lowerA : ℝ := budgetA allowance sAllowance kappaAllowance

def lowerB : ℝ := budgetB allowance sAllowance cAllowance kappaAllowance

/-- A five-term Taylor lower bound; every numerical operation is exact. -/
theorem two_lt_exp_twentyfive_div_thirtysix :
    (2 : ℝ) < Real.exp (25/36) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 25/36) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_neg_nat_mul_bound (n : ℕ) (hn : 0 < n) :
    Real.exp (-((n : ℝ) * (25/36))) < 1 / (2 : ℝ)^n := by
  rw [Real.exp_neg, Real.exp_nat_mul, ← one_div]
  exact one_div_lt_one_div_of_lt (by positivity)
    (pow_lt_pow_left₀ two_lt_exp_twentyfive_div_thirtysix (by norm_num) (by omega))

theorem exp_neg_twohundred : Real.exp (-200 : ℝ) < 1 / (2 : ℝ)^288 := by
  convert exp_neg_nat_mul_bound 288 (by decide) using 1; norm_num

theorem exp_neg_onehundred : Real.exp (-100 : ℝ) < 1 / (2 : ℝ)^144 := by
  convert exp_neg_nat_mul_bound 144 (by decide) using 1; norm_num

theorem exp_neg_fourhundred : Real.exp (-400 : ℝ) < 1 / (2 : ℝ)^576 := by
  convert exp_neg_nat_mul_bound 576 (by decide) using 1; norm_num

theorem shell_ratio_numerical : (2 : ℝ)^33 * Real.exp (-600) < 1/2 := by
  have he : Real.exp (-600 : ℝ) < 1 / (2 : ℝ)^864 := by
    convert exp_neg_nat_mul_bound 864 (by decide) using 1; norm_num
  have h := mul_lt_mul_of_pos_left he (by positivity : (0 : ℝ) < 2^33)
  norm_num at h ⊢
  linarith

/-- Pure sequence comparison after a shell majorant has been obtained.
Index zero represents the first nonzero lattice shell (n=1 in the paper). -/
theorem geometric_shell_bound (f : ℕ → ℝ) (C : ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hC : f 0 ≤ C)
    (hstep : ∀ n, f (n+1) ≤ (1/2 : ℝ) * f n) :
    Summable f ∧ (∑' n, f n) ≤ 2*C := by
  have hC0 : 0 ≤ C := (hf0 0).trans hC
  have hb : ∀ n, f n ≤ C * (1/2 : ℝ)^n := by
    intro n
    induction n with
    | zero => simpa using hC
    | succ n ih =>
      calc
        f (n+1) ≤ (1/2 : ℝ) * f n := hstep n
        _ ≤ (1/2 : ℝ) * (C * (1/2 : ℝ)^n) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = C * (1/2 : ℝ)^(n+1) := by ring
  have hs := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left C
  have hf := Summable.of_nonneg_of_le hf0 hb hs
  refine ⟨hf, (hf.tsum_le_tsum hb hs).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]
  ring

def degreeBound (D : ℕ) : ℝ :=
  50 * (D+1 : ℕ)^2 * (D.factorial : ℝ) * (20 : ℝ)^(2*D) / (2 : ℝ)^288

def pairBound : ℝ := 50 / (2 : ℝ)^144

def diagonalOneBound : ℝ := 50 / (2 : ℝ)^288

def diagonalTwoBound : ℝ := 50 / (2 : ℝ)^576

theorem degree_sixteen_bound : degreeBound 16 < allowance := by
  norm_num [degreeBound, allowance, Nat.factorial]

theorem degree_eight_bound : degreeBound 8 < allowance := by
  norm_num [degreeBound, allowance, Nat.factorial]

theorem pair_bound : pairBound < allowance := by
  norm_num [pairBound, allowance]

theorem diagonal_one_bound : diagonalOneBound < allowance := by
  norm_num [diagonalOneBound, allowance]

theorem diagonal_two_bound : diagonalTwoBound < allowance := by
  norm_num [diagonalTwoBound, allowance]

theorem five_errors_fit_common_allowance :
    degreeBound 16 < allowance ∧ degreeBound 8 < allowance ∧
    pairBound < allowance ∧ diagonalOneBound < allowance ∧
    diagonalTwoBound < allowance :=
  ⟨degree_sixteen_bound, degree_eight_bound, pair_bound,
    diagonal_one_bound, diagonal_two_bound⟩

theorem lowerA_exact : lowerA =
    8183525179652905540939777339971061478405006776240354085927 /
    24266058979973529600000000000000000000000000000000000000000 := by
  norm_num [lowerA, budgetA, sAllowance, kappaAllowance, allowance, eta,
    rowCost, delta, c9, c3, c4]

theorem lowerB_exact : lowerB =
    19326695545052423240596864889482025919460640111495553399803410151 /
    1213302924732617621356765299867648000000000000000000000000000000000 := by
  norm_num [lowerB, budgetB, sAllowance, cAllowance, kappaAllowance,
    allowance, alpha, eta, rowCost, delta, c9, c3, c4]

theorem lowerA_gt_third : (1/3 : ℝ) < 337241/1000000 ∧
    (337241/1000000 : ℝ) < lowerA := by
  rw [lowerA_exact]
  norm_num

theorem lowerB_pos : (0 : ℝ) < 15928/1000000 ∧
    (15928/1000000 : ℝ) < lowerB := by
  rw [lowerB_exact]
  norm_num

/-- Safe substitution of the uniform allowance in both scalar budgets.
All physical error and density hypotheses remain visible. -/
theorem budget_lower_bounds (e2 e4 s c k : ℝ)
    (he2 : e2 ≤ allowance) (he4 : e4 ≤ allowance)
    (hs0 : 0 ≤ s) (hs : s ≤ sAllowance)
    (hc0 : 0 ≤ c) (hc : c ≤ cAllowance)
    (hk0 : 0 ≤ k) (hk : k ≤ kappaAllowance) :
    lowerA ≤ budgetA e2 s k ∧ lowerB ≤ budgetB e4 s c k := by
  have hd : 0 ≤ delta := by norm_num [delta]
  have hc3 : 0 ≤ c3 := by norm_num [c3]
  have hc4 : 0 ≤ c4 := by norm_num [c4]
  have hc9 : 0 ≤ c9 := by norm_num [c9]
  have ha : 0 ≤ alpha := by norm_num [alpha, c9]
  have hsA0 : 0 ≤ sAllowance := hs0.trans hs
  have hcA0 : 0 ≤ cAllowance := hc0.trans hc
  have ht : 0 ≤ c9 + (delta + k) * c3 := by positivity
  have hsk : s * (c9 + (delta + k) * c3) ≤
      sAllowance * (c9 + (delta + kappaAllowance) * c3) := by gcongr
  have hs2 : s^2 ≤ sAllowance^2 := by gcongr
  have hsc : s*c * (c9 + (delta + k) * c3) ≤
      sAllowance*cAllowance * (c9 + (delta + kappaAllowance) * c3) := by gcongr
  have hs2c : s^2*c ≤ sAllowance^2*cAllowance := by gcongr
  have ha4 := mul_le_mul_of_nonneg_left (add_le_add_left he4 1) ha
  constructor
  · unfold lowerA budgetA
    nlinarith [mul_le_mul_of_nonneg_left hs2 (mul_nonneg hd hc4)]
  · unfold lowerB budgetB
    nlinarith [mul_le_mul_of_nonneg_left hs2c (by positivity : 0 ≤ 2*delta*c4)]

/-- This scalar implication is ready for a separately established physical
master inequality; no Hamiltonian is defined by the budget. -/
theorem scalar_master_implies_third (H Hsq K S4 A B : ℝ)
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hS4 : 0 ≤ S4)
    (hA : lowerA ≤ A) (hB : lowerB ≤ B)
    (hmaster : K + A*H + B*S4 ≤ Hsq) : H/3 ≤ Hsq := by
  have ha : (1/3 : ℝ) ≤ A :=
    (lowerA_gt_third.1.trans lowerA_gt_third.2).le.trans hA
  have hb : 0 ≤ B := (lowerB_pos.1.trans lowerB_pos.2).le.trans hB
  nlinarith [mul_nonneg hb hS4, mul_le_mul_of_nonneg_right ha hH]


#print axioms two_lt_exp_twentyfive_div_thirtysix
#print axioms exp_neg_twohundred
#print axioms shell_ratio_numerical
#print axioms geometric_shell_bound
#print axioms five_errors_fit_common_allowance
#print axioms lowerA_exact
#print axioms lowerB_exact
#print axioms lowerA_gt_third
#print axioms lowerB_pos
#print axioms budget_lower_bounds
#print axioms scalar_master_implies_third

end TorusLean.Shared.BosonSystole20Scalar
