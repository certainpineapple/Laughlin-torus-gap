import torus.shared.LLLSliceReconstruction
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.LLLTensorReconstruction

open TorusLean.Shared.LLLSliceReconstruction

/-- All ordered words, with head/tail equivalence including the empty tail. -/
def wordHeadTailEquiv (I : Type*) (N : ℕ) :
    (Fin (N+1) → I) ≃ I × (Fin N → I) where
  toFun w := (w 0, Fin.tail w)
  invFun p := Fin.cons p.1 p.2
  left_inv w := Fin.cons_self_tail w
  right_inv p := by rcases p with ⟨i,w⟩; simp

theorem sum_words_succ {I : Type*} [Fintype I] (N : ℕ)
    (F : (Fin (N+1) → I) → ℂ) :
    ∑ w, F w = ∑ i, ∑ w : Fin N → I, F (Fin.cons i w) := by
  rw [Fintype.sum_equiv (wordHeadTailEquiv I N) F
    (fun p => F (Fin.cons p.1 p.2)) (fun w => by simp [wordHeadTailEquiv])]
  exact Fintype.sum_prod_type _

/-- Every all-point physical slice function has a finite ordered tensor
expansion. No integrability, joint holomorphy or coefficient regularity premise. -/
theorem slices_tensor_expansion (G : Geometry) (theta : Twist)
    {I : Type*} [Fintype I] (b : Module.Basis I ℂ (LLL G theta 1))
    (N : ℕ) (f : (Fin N → ℂ) → ℂ) (hf : HasLLLSlices G theta N f) :
    ∃ c : (Fin N → I) → ℂ, ∀ z : Fin N → ℂ,
      f z = ∑ w : Fin N → I, c w * ∏ a, (b (w a)).val (z a) := by
  classical
  induction N with
  | zero =>
    refine ⟨fun _ => f (fun a => Fin.elim0 a), ?_⟩
    intro z
    have hz : z = (fun a : Fin 0 => Fin.elim0 a) := Subsingleton.elim _ _
    subst z
    simp
  | succ N ih =>
    have hex : ∀ i : I, ∃ c : (Fin N → I) → ℂ, ∀ y : Fin N → ℂ,
        b.repr (headSection G theta N f hf y) i =
          ∑ w, c w * ∏ a, (b (w a)).val (y a) := by
      intro i
      exact ih (fun y => b.coord i (headSection G theta N f hf y))
        (head_functional_has_slices G theta N f hf (b.coord i))
    choose c hc using hex
    refine ⟨fun w => c (w 0) (Fin.tail w), ?_⟩
    intro z
    conv_lhs => rw [← Fin.cons_self_tail z]
    rw [head_basis_expansion G theta N b f hf, sum_words_succ]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Fin.cons_zero, Fin.tail_cons, Fin.prod_univ_succ, Fin.cons_succ, Fin.tail]
    ring

#print axioms sum_words_succ
#print axioms slices_tensor_expansion

end TorusLean.Shared.LLLTensorReconstruction
