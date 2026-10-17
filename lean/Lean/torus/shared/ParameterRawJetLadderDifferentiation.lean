import torus.shared.ParameterRawJetLadderCalculus

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ParameterCellAdjoint
open scoped ComplexConjugate BigOperators ContDiff

theorem jetPolynomial_wirtinger (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (j : ℕ) (R : ℂ) :
    parameterWirtinger (jetPolynomial F j) R = jetPolynomial (deriv F) j R := by
  have hD (n : ℕ) : Differentiable ℂ (iteratedDeriv n F) :=
    hF.contDiff.differentiable_iteratedDeriv' n
  have hc : Differentiable ℝ (fun z : ℂ => -conj z) := Complex.conjCLE.differentiable.neg
  have hi (n : ℕ) : Differentiable ℝ (fun z : ℂ =>
      (j.choose n : ℂ) * iteratedDeriv n F z * (-conj z)^(j-n)) :=
    (((hD n).restrictScalars ℝ).const_mul _).mul (hc.pow _)
  unfold jetPolynomial
  rw [wirtinger_sum (Finset.range (j+1)) (fun n z => (j.choose n : ℂ)*iteratedDeriv n F z*(-conj z)^(j-n)) (fun n _ => hi n) R]
  apply Finset.sum_congr rfl
  intro n hn
  rw [wirtinger_mul (fun z => (j.choose n : ℂ)*iteratedDeriv n F z) (fun z => (-conj z)^(j-n)) (((hD n).restrictScalars ℝ).const_mul _) (hc.pow _) R,
    (wirtinger_const_mul (j.choose n : ℂ) (iteratedDeriv n F) ((hD n).restrictScalars ℝ) R).1,
    (wirtinger_holomorphic _ (hD n) R).1, (wirtinger_pow (fun z => -conj z) hc (j-n) R).1,
    (wirtinger_neg_conj R).1]
  simp only [mul_zero, add_zero]
  rw [← iteratedDeriv_succ, iteratedDeriv_succ']

theorem jetPolynomial_wirtingerBar_sum (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (j : ℕ) (R : ℂ) :
    parameterWirtingerBar (jetPolynomial F j) R =
    -∑ n ∈ Finset.range (j+1), (j.choose n : ℂ) * ((j-n : ℕ) : ℂ) *
      iteratedDeriv n F R * (-conj R)^(j-n-1) := by
  have hD (n : ℕ) : Differentiable ℂ (iteratedDeriv n F) :=
    hF.contDiff.differentiable_iteratedDeriv' n
  have hc : Differentiable ℝ (fun z : ℂ => -conj z) := Complex.conjCLE.differentiable.neg
  have hi (n : ℕ) : Differentiable ℝ (fun z : ℂ =>
      (j.choose n : ℂ) * iteratedDeriv n F z * (-conj z)^(j-n)) :=
    (((hD n).restrictScalars ℝ).const_mul _).mul (hc.pow _)
  unfold jetPolynomial
  rw [wirtingerBar_sum (Finset.range (j+1)) (fun n z => (j.choose n : ℂ)*iteratedDeriv n F z*(-conj z)^(j-n)) (fun n _ => hi n) R]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [wirtingerBar_mul (fun z => (j.choose n : ℂ)*iteratedDeriv n F z) (fun z => (-conj z)^(j-n)) (((hD n).restrictScalars ℝ).const_mul _) (hc.pow _) R,
    (wirtinger_const_mul (j.choose n : ℂ) (iteratedDeriv n F) ((hD n).restrictScalars ℝ) R).2,
    (wirtinger_holomorphic _ (hD n) R).2, (wirtinger_pow (fun z => -conj z) hc (j-n) R).2,
    (wirtinger_neg_conj R).2]
  ring

end TorusLean.Shared.ParameterRawJetLadder
