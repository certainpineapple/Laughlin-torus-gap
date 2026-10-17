import torus.shared.BosonFiniteCertificateNatCOMLower
import torus.shared.BosonFiniteCertificateNatOccupationInner

/-!
# Actual natural-orbital COM occupation adjoints

The actual polynomial derivations on all natural orbital labels are adjoint
for the genuine factorial-weighted occupation form. Each individual polynomial
has finitely many variables. Restriction to a sufficiently large finite sum is
therefore an exact identity on that polynomial, not an orbital truncation of
the operator or an invariant finite-dimensional domain assumption.

The proof uses the separately proved creation/annihilation adjoints and real
COM coefficients. No commutation relation is used to infer an adjoint relation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open scoped BigOperators ComplexConjugate
open TorusLean.Boson

private theorem natCOM_derivation_sum_apply (s : Finset ℕ)
    (D : ℕ → Derivation ℂ (Core ℕ ℂ) (Core ℕ ℂ)) (f : Core ℕ ℂ) :
    (∑ j ∈ s, D j) f = ∑ j ∈ s, D j f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj, Derivation.add_apply, ih]

/-- A finite variable bound gives an exact one-body expansion of the actual
derivation on this input polynomial. -/
private theorem natCOM_mkDerivation_finite_sum (a : ℕ → Core ℕ ℂ)
    (m : ℕ) (f : Core ℕ ℂ) (hf : f.vars ⊆ Finset.range m) :
    (MvPolynomial.mkDerivation ℂ a) f =
      ∑ j ∈ Finset.range m, a j * annihilate j f := by
  classical
  let D : Derivation ℂ (Core ℕ ℂ) (Core ℕ ℂ) :=
    ∑ j ∈ Finset.range m, a j • MvPolynomial.pderiv j
  have hgen : ∀ i ∈ f.vars,
      (MvPolynomial.mkDerivation ℂ a) (MvPolynomial.X i) = D (MvPolynomial.X i) := by
    intro i hi
    rw [MvPolynomial.mkDerivation_X]
    change a i = (∑ j ∈ Finset.range m, a j • MvPolynomial.pderiv j) (MvPolynomial.X i)
    rw [natCOM_derivation_sum_apply, Finset.sum_eq_single i]
    · simp only [Derivation.smul_apply, MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one]
    · intro j hj hji
      rw [Derivation.smul_apply, MvPolynomial.pderiv_X_of_ne (Ne.symm hji), smul_zero]
    · intro hi'
      exact (hi' (hf hi)).elim
  calc
    (MvPolynomial.mkDerivation ℂ a) f = D f :=
      MvPolynomial.derivation_eq_of_forall_mem_vars hgen
    _ = ∑ j ∈ Finset.range m, a j * annihilate j f := by
      dsimp only [D]
      rw [natCOM_derivation_sum_apply]
      simp only [Derivation.smul_apply, smul_eq_mul, annihilate, Derivation.coeFn_coe]

/-- Locally finite exact expansion of the genuine raising operator. -/
theorem canonicalCOMRaiseNat_finite_sum (m : ℕ) (f : Core ℕ ℂ)
    (hf : f.vars ⊆ Finset.range m) :
    canonicalCOMRaiseNat f = ∑ j ∈ Finset.range m,
      (Real.sqrt (j+1 : ℝ) : ℂ) • create (j+1) (annihilate j f) := by
  change (MvPolynomial.mkDerivation ℂ (fun j : ℕ =>
    (Real.sqrt (j+1 : ℝ) : ℂ) • (MvPolynomial.X (j+1) : Core ℕ ℂ))) f = _
  rw [natCOM_mkDerivation_finite_sum _ m f hf]
  apply Finset.sum_congr rfl
  intro j hj
  simp [create, smul_mul_assoc]

/-- Locally finite exact lowering expansion, reindexed so that each term is
the actual adjoint of the raising term with the same index. The zero orbital
contributes zero before this reindexing. -/
theorem canonicalCOMLowerNat_finite_sum (m : ℕ) (g : Core ℕ ℂ)
    (hg : g.vars ⊆ Finset.range (m+1)) :
    canonicalCOMLowerNat g = ∑ j ∈ Finset.range m,
      (Real.sqrt (j+1 : ℝ) : ℂ) • create j (annihilate (j+1) g) := by
  change (MvPolynomial.mkDerivation ℂ (fun j : ℕ =>
    (Real.sqrt (j : ℝ) : ℂ) • (MvPolynomial.X (j-1) : Core ℕ ℂ))) g = _
  rw [natCOM_mkDerivation_finite_sum _ (m+1) g hg, Finset.sum_range_succ']
  simp only [Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_smul,
    zero_mul, add_zero, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro j hj
  simp [create, smul_mul_assoc]

/-- The genuine COM raising and lowering derivations are adjoint on the
entire finite polynomial core over natural orbital labels. -/
theorem canonicalCOMRaiseNat_adjoint (f g : Core ℕ ℂ) :
    natOccupationInner (canonicalCOMRaiseNat f) g =
      natOccupationInner f (canonicalCOMLowerNat g) := by
  classical
  let m : ℕ := (f.vars ∪ g.vars).sup id + 1
  have hf : f.vars ⊆ Finset.range m := by
    intro i hi
    exact Finset.subset_range_sup_succ (f.vars ∪ g.vars)
      (Finset.mem_union_left _ hi)
  have hg : g.vars ⊆ Finset.range (m+1) := by
    intro i hi
    have hm : i < m := Finset.mem_range.mp
      (Finset.subset_range_sup_succ (f.vars ∪ g.vars) (Finset.mem_union_right _ hi))
    exact Finset.mem_range.mpr (by omega)
  rw [canonicalCOMRaiseNat_finite_sum m f hf, canonicalCOMLowerNat_finite_sum m g hg,
    natOccupationInner_sum_left, natOccupationInner_sum_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [natOccupationInner_smul_left, natOccupationInner_smul_right,
    nat_create_adjoint, nat_annihilate_adjoint]
  simp

/-- The reverse adjoint identity is obtained from conjugate symmetry. -/
theorem canonicalCOMLowerNat_adjoint (f g : Core ℕ ℂ) :
    natOccupationInner (canonicalCOMLowerNat f) g =
      natOccupationInner f (canonicalCOMRaiseNat g) := by
  have h := congrArg star (canonicalCOMRaiseNat_adjoint g f)
  simpa only [natOccupationInner_conj_symm] using h.symm

/-- Every finite power of the actual raising operator has the corresponding
power of the actual lowering operator as its occupation adjoint. -/
theorem canonicalCOMRaiseNat_iterate_adjoint (n : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f) g =
      natOccupationInner f ((canonicalCOMLowerNat : Core ℕ ℂ → Core ℕ ℂ)^[n] g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', canonicalCOMRaiseNat_adjoint, ih,
      Function.iterate_succ_apply]

theorem canonicalCOMLowerNat_iterate_adjoint (n : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner ((canonicalCOMLowerNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f) g =
      natOccupationInner f ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] g) := by
  have h := congrArg star (canonicalCOMRaiseNat_iterate_adjoint n g f)
  simpa only [natOccupationInner_conj_symm] using h.symm

/-- Every positive-level genuine COM descendant is orthogonal to every
actual lowering vacuum. Neither particle number nor orbital degree is a
premise of this full-core statement. -/
theorem canonicalCOMRaiseNat_iterate_orthogonal_of_lower_eq_zero
    (n : ℕ) (f g : Core ℕ ℂ) (hL : canonicalCOMLowerNat g = 0) :
    natOccupationInner ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] f) g = 0 := by
  rw [Function.iterate_succ_apply', canonicalCOMRaiseNat_adjoint, hL,
    natOccupationInner_zero_right]

theorem canonicalCOMRaiseNat_iterate_orthogonal_of_lower_eq_zero_symm
    (n : ℕ) (f g : Core ℕ ℂ) (hL : canonicalCOMLowerNat g = 0) :
    natOccupationInner g ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] f) = 0 := by
  have h := congrArg star
    (canonicalCOMRaiseNat_iterate_orthogonal_of_lower_eq_zero n f g hL)
  simpa only [natOccupationInner_conj_symm, star_zero] using h

#print axioms canonicalCOMRaiseNat_finite_sum
#print axioms canonicalCOMLowerNat_finite_sum
#print axioms canonicalCOMRaiseNat_adjoint
#print axioms canonicalCOMLowerNat_adjoint
#print axioms canonicalCOMRaiseNat_iterate_adjoint
#print axioms canonicalCOMLowerNat_iterate_adjoint
#print axioms canonicalCOMRaiseNat_iterate_orthogonal_of_lower_eq_zero
#print axioms canonicalCOMRaiseNat_iterate_orthogonal_of_lower_eq_zero_symm
end TorusLean.BosonFiniteCertificate
