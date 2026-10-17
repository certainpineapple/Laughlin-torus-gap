import torus.shared.LLLFiniteEvaluation
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.LLLSliceReconstruction

open TorusLean.Shared.LLLFiniteEvaluation

/-- Every coordinate slice at every full universal-cover configuration is
an actual physical LLL section. No coefficient or image condition occurs. -/
def HasLLLSlices (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin N → ℂ) → ℂ) : Prop :=
  ∀ a : Fin N, ∀ z : Fin N → ℂ, ∃ h : LLL G theta 1,
    ∀ t : ℂ, h.val t = f (Function.update z a t)

def headSection (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin (N+1) → ℂ) → ℂ) (hf : HasLLLSlices G theta (N+1) f)
    (y : Fin N → ℂ) : LLL G theta 1 :=
  Classical.choose (hf 0 (Fin.cons 0 y))

theorem headSection_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin (N+1) → ℂ) → ℂ) (hf : HasLLLSlices G theta (N+1) f)
    (y : Fin N → ℂ) (t : ℂ) :
    (headSection G theta N f hf y).val t = f (Fin.cons t y) := by
  simpa only [headSection, Fin.update_cons_zero] using Classical.choose_spec (hf 0 (Fin.cons 0 y)) t

/-- Any fixed algebraic coordinate of the head section retains every actual
tail LLL slice. This is proved from the original slice hypothesis. -/
theorem head_functional_has_slices (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin (N+1) → ℂ) → ℂ) (hf : HasLLLSlices G theta (N+1) f)
    (K : LLL G theta 1 →ₗ[ℂ] ℂ) :
    HasLLLSlices G theta N (fun y => K (headSection G theta N f hf y)) := by
  intro a y
  apply functional_preserves_section G theta K
    (fun x => headSection G theta N f hf (Function.update y a x))
  intro R
  obtain ⟨g, hg⟩ := hf a.succ (Fin.cons R y)
  refine ⟨g, ?_⟩
  intro x
  rw [headSection_apply, Fin.cons_update]
  exact hg x

/-- Exact first-coordinate expansion in any basis of the whole actual LLL. -/
theorem head_basis_expansion (G : Geometry) (theta : Twist) (N : ℕ)
    {I : Type*} [Fintype I] (b : Module.Basis I ℂ (LLL G theta 1))
    (f : (Fin (N+1) → ℂ) → ℂ) (hf : HasLLLSlices G theta (N+1) f)
    (y : Fin N → ℂ) (t : ℂ) :
    f (Fin.cons t y) =
      ∑ i, b.repr (headSection G theta N f hf y) i * (b i).val t := by
  have h := congrArg (fun g : LLL G theta 1 => lllEvaluationLinearMap G theta 1 t g)
    (b.sum_repr (headSection G theta N f hf y))
  simp only [map_sum, map_smul] at h
  change (∑ i, b.repr (headSection G theta N f hf y) i * (b i).val t) =
    (headSection G theta N f hf y).val t at h
  rw [headSection_apply] at h
  exact h.symm

#print axioms headSection_apply
#print axioms head_functional_has_slices
#print axioms head_basis_expansion

end TorusLean.Shared.LLLSliceReconstruction
