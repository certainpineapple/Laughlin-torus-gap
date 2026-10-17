import torus.shared.PhysicalFermionExteriorOccupation

/-! Explicit Slater determinants, arbitrary ordered-word coordinates, and the
vacuum and overfull boundaries of the normalized exterior equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionExterior
open scoped ComplexConjugate
open TorusLean.Shared.PhysicalFermionCarrier OAI.Laughlin.Fock
variable {I : Type*} [Fintype I] [LinearOrder I] {N Q : ℕ}

lemma permutationSign_conj (σ : Equiv.Perm (Fin N)) :
    conj (permutationSign σ) = permutationSign σ := by
  simp [permutationSign]

/-- The wedge of orbital mode vectors has only real signed occupation coefficients. -/
lemma wedgeWord_repr_conj (w : Fin N → I) (A : Occupation I N) :
    conj ((exteriorBasis I N).repr (wedgeWord w) A) =
      (exteriorBasis I N).repr (wedgeWord w) A := by
  classical
  by_cases hw : Function.Injective w
  · obtain ⟨B, σ, rfl⟩ := exists_canonicalWord_perm w hw
    rw [wedgeWord_perm, wedgeWord_canonical]
    by_cases hAB : B = A <;> simp [Module.Basis.repr_self, Finsupp.single_apply, hAB, permutationSign_conj]
  · have hz : wedgeWord w = 0 := by
      apply (exteriorPower.ιMulti ℂ N).map_eq_zero_of_not_injective
      exact fun h => hw (Function.Injective.of_comp h)
    simp [hz]

/-- Arbitrary ordered coefficients are the official vacuum-to-wedge matrix
coefficient, with exactly one factor 1/√N!. -/
theorem normalizedExterior_word_inner (x : Exterior (Fin (Q+1)) N) (w : Fin N → Fin (Q+1)) :
    (normalizedExterior (Fin (Q+1)) N x).val w =
      occupationInner Q (wedgeWord w : Space Q) (x : Space Q) / sqrtFactorial N := by
  rw [occupationInner_exterior]
  change (sqrtFactorial N)⁻¹ * exteriorOrdered x w = _
  simp only [exteriorOrdered, wedgeWord_repr_conj]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  ring

/-- The usual determinant of an arbitrary ordered orbital family. -/
def slaterCoefficient (v : Fin N → I → ℂ) (w : Fin N → I) : ℂ :=
  (Matrix.of fun i j => v i (w j)).det

lemma slaterCoefficient_alternating (v : Fin N → I → ℂ) : IsAlternating (slaterCoefficient v) := by
  intro σ w
  simpa only [slaterCoefficient, Function.comp_def, permutationSign, Matrix.submatrix,
    Matrix.of_apply, id_eq] using Matrix.det_permute' σ (Matrix.of fun i j => v i (w j))

/-- The exterior synthesis is exactly the determinant Slater convention,
not an arbitrarily chosen orthonormal identification. -/
theorem exteriorOrdered_ιMulti (v : Fin N → I → ℂ) :
    exteriorOrdered (exteriorPower.ιMulti ℂ N v) = slaterCoefficient v := by
  apply alternating_ext (exteriorOrdered_alternating _) (slaterCoefficient_alternating v)
  intro A
  rw [exteriorOrdered_canonical, exteriorBasis, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply, Pi.basisFun_repr]
  rfl

theorem normalizedExterior_ιMulti (v : Fin N → I → ℂ) (w : Fin N → I) :
    (normalizedExterior I N (exteriorPower.ιMulti ℂ N v)).val w =
      (Matrix.of fun i j => v i (w j)).det / sqrtFactorial N := by
  change (sqrtFactorial N)⁻¹ * exteriorOrdered (exteriorPower.ιMulti ℂ N v) w = _
  rw [exteriorOrdered_ιMulti]
  exact mul_comm _ _

/-- Empty wedge has one empty ordered coefficient equal to one. -/
theorem normalizedExterior_vacuum (w : Fin 0 → I) :
    (normalizedExterior I 0 (wedgeWord (Fin.elim0 : Fin 0 → I))).val w = 1 := by
  let A : Occupation I 0 := ⟨∅, rfl⟩
  have hw : w = canonicalWord A := Subsingleton.elim _ _
  have he : (Fin.elim0 : Fin 0 → I) = canonicalWord A := Subsingleton.elim _ _
  rw [hw, he, wedgeWord_canonical, normalizedExterior_canonical]
  simp [Module.Basis.repr_self]

/-- Above the one-particle dimension the exterior sector itself is zero. -/
theorem exterior_zero_above_dimension (h : Fintype.card I < N) (x : Exterior I N) : x = 0 := by
  apply (exteriorBasis I N).ext_elem
  intro A
  have hc := Finset.card_le_card (Finset.subset_univ A.val)
  rw [Finset.card_univ, A.property] at hc
  exact False.elim (Nat.not_le_of_lt h hc)

#print axioms normalizedExterior_word_inner
#print axioms exteriorOrdered_ιMulti
#print axioms normalizedExterior_ιMulti
#print axioms normalizedExterior_vacuum
#print axioms exterior_zero_above_dimension
end TorusLean.Shared.PhysicalFermionExterior
