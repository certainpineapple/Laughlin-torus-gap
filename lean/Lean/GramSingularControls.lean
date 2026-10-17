/- Exact finite controls for M2a, not a Schur-checker soundness proof. -/
import GramCongruence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace TorusLean.M2

def singularW : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else 0)

def indefiniteA : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else -1)

def secondVector : Fin 2 → ℂ := fun i => if i = 1 then 1 else 0

theorem singularW_psd : singularW.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem indefiniteA_hermitian : indefiniteA.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [IsSelfAdjoint]

theorem indefiniteA_not_psd : ¬ indefiniteA.PosSemidef := by
  intro h
  have hn := h.diag_nonneg (i := (1 : Fin 2))
  norm_num [indefiniteA] at hn

theorem singular_sandwich_eq : singularW * indefiniteA * singularWᴴ = singularW := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singularW, indefiniteA, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal, Fin.sum_univ_two]

theorem singular_sandwich_psd : (singularW * indefiniteA * singularWᴴ).PosSemidef := by
  rw [singular_sandwich_eq]
  exact singularW_psd

theorem singular_gram_psd :
    ((singularWᴴ * singularW) * indefiniteA * (singularWᴴ * singularW)).PosSemidef :=
  (complex_gram_congruence_iff singularW indefiniteA indefiniteA_hermitian).mpr
    singular_sandwich_psd

theorem singularW_kills_second : singularW *ᵥ secondVector = 0 := by
  ext i
  fin_cases i <;>
    norm_num [singularW, secondVector, Matrix.mulVec, Matrix.diagonal, Fin.sum_univ_two]

theorem singularW_not_injective : ¬ Function.Injective singularW.mulVec := by
  intro h
  have he : secondVector = 0 := h (by rw [singularW_kills_second, Matrix.mulVec_zero])
  have hh := congrFun he (1 : Fin 2)
  norm_num [secondVector] at hh

def zeroPivotBad : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if i = j then 0 else 1

theorem zero_pivot_nonzero_row_not_psd : ¬ zeroPivotBad.PosSemidef := by
  intro h
  have hn := h.dotProduct_mulVec_nonneg (fun i : Fin 2 => if i = 0 then 1 else -1)
  norm_num [zeroPivotBad, dotProduct, Matrix.mulVec, Fin.sum_univ_two] at hn

#print axioms singularW_psd
#print axioms indefiniteA_hermitian
#print axioms indefiniteA_not_psd
#print axioms singular_sandwich_eq
#print axioms singular_sandwich_psd
#print axioms singular_gram_psd
#print axioms singularW_kills_second
#print axioms singularW_not_injective
#print axioms zero_pivot_nonzero_row_not_psd

end TorusLean.M2
