import torus.shared.PhysicalFermionExteriorCore
import OAI.Analysis.Laughlin.Fock.Inner

/-! Identification with the unmodified OAI occupationBasis and occupationInner. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionExterior
open scoped ComplexConjugate
open OAI.Laughlin.Fock

variable {Q N : ℕ}

/-- No factorial is hidden in the official occupation-to-exterior basis bridge. -/
theorem occupationBasis_eq_exteriorBasis (A : Occupation (Fin (Q+1)) N) :
    occupationBasis Q A.val = (exteriorBasis (Fin (Q+1)) N A : Space Q) :=
  ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun ℂ (Fin (Q+1))) A

/-- The ambient Fock coordinates of a fixed-degree exterior vector. -/
theorem occupation_repr_exterior (x : Exterior (Fin (Q+1)) N) (B : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (x : Space Q) B =
      if h : B.card = N then (exteriorBasis (Fin (Q+1)) N).repr x ⟨B,h⟩ else 0 := by
  classical
  have hx : (x : Space Q) = ∑ A : Occupation (Fin (Q+1)) N,
      (exteriorBasis (Fin (Q+1)) N).repr x A • occupationBasis Q A.val := by
    conv_lhs => rw [← (exteriorBasis (Fin (Q+1)) N).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, occupationBasis_eq_exteriorBasis]
  rw [hx]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  split_ifs with hB
  · rw [Finset.sum_eq_single (⟨B,hB⟩ : Occupation (Fin (Q+1)) N)]
    · simp
    · intro A _ hA
      have hv : A.val ≠ B := fun h => hA (Subtype.ext h)
      simp [hv]
    · simp
  · apply Finset.sum_eq_zero
    intro A _
    have hv : A.val ≠ B := by
      intro h
      exact hB (h ▸ A.property)
    simp [hv]

/-- All coordinates in the other number sectors vanish. -/
theorem occupation_repr_exterior_other (x : Exterior (Fin (Q+1)) N)
    (B : Finset (Fin (Q+1))) (h : B.card ≠ N) :
    (occupationBasis Q).repr (x : Space Q) B = 0 := by
  simp [occupation_repr_exterior, h]

/-- The original OAI inner product is exactly the exterior-sector coordinate
sum; the sum over all Finsets has been reduced by a proved grading statement. -/
theorem occupationInner_exterior (x y : Exterior (Fin (Q+1)) N) :
    occupationInner Q (x : Space Q) (y : Space Q) =
      ∑ A : Occupation (Fin (Q+1)) N,
        conj ((exteriorBasis (Fin (Q+1)) N).repr x A) *
          (exteriorBasis (Fin (Q+1)) N).repr y A := by
  classical
  unfold occupationInner
  rw [← Fintype.sum_subtype_add_sum_subtype (p := fun A : Finset (Fin (Q+1)) => A.card = N)]
  have hz : (∑ A : {A : Finset (Fin (Q+1)) // ¬ A.card = N},
      star ((occupationBasis Q).repr (x : Space Q) A.val) *
        (occupationBasis Q).repr (y : Space Q) A.val) = 0 := by
    apply Finset.sum_eq_zero
    intro A _
    rw [occupation_repr_exterior_other x A.val A.property, star_zero, zero_mul]
  rw [hz, add_zero]
  let e : {A : Finset (Fin (Q+1)) // A.card = N} ≃ Occupation (Fin (Q+1)) N := Equiv.refl _
  apply Fintype.sum_equiv e
  intro A
  simp only [occupation_repr_exterior, A.property, dif_pos, Complex.star_def]
  rfl

/-- Onto normalized ordered tensors with the original OAI inner product. -/
theorem normalizedExterior_occupationInner (x y : Exterior (Fin (Q+1)) N) :
    (∑ w, conj ((normalizedExterior (Fin (Q+1)) N x).val w) *
      (normalizedExterior (Fin (Q+1)) N y).val w) =
        occupationInner Q (x : Space Q) (y : Space Q) := by
  rw [normalizedExterior_inner, occupationInner_exterior]

#print axioms occupation_repr_exterior
#print axioms occupationInner_exterior
#print axioms normalizedExterior_occupationInner
end TorusLean.Shared.PhysicalFermionExterior
