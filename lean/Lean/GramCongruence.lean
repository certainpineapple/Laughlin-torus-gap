/- M2a: finite matrix congruence with the full Gram kernel retained.
   No physical periodization or torus gap hypotheses appear. -/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace TorusLean.M2

section General
variable {m n : Type*} [Fintype m] [Fintype n]
variable {R : Type*} [Field R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem range_gram_eq_range_adjoint (W : Matrix m n R) :
    LinearMap.range (Wᴴ * W).mulVecLin = LinearMap.range Wᴴ.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range W.mulVecLin Wᴴ.mulVecLin
  · change (Wᴴ * W).rank = Wᴴ.rank
    rw [Matrix.rank_conjTranspose_mul_self, Matrix.rank_conjTranspose]

theorem adjoint_vector_is_gram_vector (W : Matrix m n R) (v : m → R) :
    ∃ x : n → R, (Wᴴ * W) *ᵥ x = Wᴴ *ᵥ v := by
  have hv : Wᴴ *ᵥ v ∈ LinearMap.range Wᴴ.mulVecLin := ⟨v, rfl⟩
  rw [← range_gram_eq_range_adjoint W] at hv
  exact hv

omit [PartialOrder R] [StarOrderedRing R] in
theorem sandwich_quadratic (W : Matrix m n R) (A : Matrix n n R) (v : m → R) :
    star v ⬝ᵥ ((W * A * Wᴴ) *ᵥ v) =
      star (Wᴴ *ᵥ v) ⬝ᵥ (A *ᵥ (Wᴴ *ᵥ v)) := by
  simp only [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec, vecMul_vecMul]

theorem gram_congruence_iff (W : Matrix m n R) (A : Matrix n n R)
    (hA : A.IsHermitian) :
    ((Wᴴ * W) * A * (Wᴴ * W)).PosSemidef ↔ (W * A * Wᴴ).PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (by simpa only [conjTranspose_conjTranspose] using
        Matrix.isHermitian_conjTranspose_mul_mul Wᴴ hA) ?_
    intro v
    obtain ⟨x, hx⟩ := adjoint_vector_is_gram_vector W v
    have hg : (Wᴴ * W).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self W
    have hq := h.dotProduct_mulVec_nonneg x
    have heq : star x ⬝ᵥ (((Wᴴ * W) * A * (Wᴴ * W)) *ᵥ x) =
        star ((Wᴴ * W) *ᵥ x) ⬝ᵥ (A *ᵥ ((Wᴴ * W) *ᵥ x)) := by
      simpa only [hg.eq] using sandwich_quadratic (Wᴴ * W) A x
    rw [heq, hx] at hq
    rw [sandwich_quadratic]
    exact hq
  · intro h
    have hc := h.conjTranspose_mul_mul_same W
    simpa only [Matrix.mul_assoc] using hc

end General

theorem complex_gram_congruence_iff {m n : Type*} [Fintype m] [Fintype n]
    (W : Matrix m n ℂ) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ((Wᴴ * W) * A * (Wᴴ * W)).PosSemidef ↔ (W * A * Wᴴ).PosSemidef :=
  gram_congruence_iff W A hA

#print axioms range_gram_eq_range_adjoint
#print axioms adjoint_vector_is_gram_vector
#print axioms sandwich_quadratic
#print axioms gram_congruence_iff
#print axioms complex_gram_congruence_iff

end TorusLean.M2
