import torus.shared.BosonFiniteCertificateNatFourDescendantCore

/-! The original finite COM weighted average with explicit source basis and
coordinates. The true operator, degree cutoff, descendant forms and exact
weight are unchanged. This aligns source parameters before entering the form. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFour_COM_source_matrix_form_explicit {r n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (C : Matrix (Fin n) (Fin r) ℚ)
    (hN : ∀ x : Fin r → ℂ,
      (natFourWordBlock basis (complexify C *ᵥ x)).IsHomogeneous 4)
    (hd : ∀ x : Fin r → ℂ,
      (natFourWordBlock basis (complexify C *ᵥ x)).IsWeightedHomogeneous id d)
    (F : ℕ → Matrix (Fin r) (Fin r) ℚ)
    (hF : ∀ k, k<17-d → ∀ x y : Fin r → ℂ,
      natOccupationInner
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k]
          (natFourWordBlock basis (complexify C *ᵥ x)))
        (canonicalNatFourOriginalOperator
          ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k]
            (natFourWordBlock basis (complexify C *ᵥ y))))=
      star x ⬝ᵥ (complexify (F k) *ᵥ y))
    (A : Matrix (Fin r) (Fin r) ℚ)
    (hA : (∑ k ∈ Finset.range (17-d), natFourOriginalCOMWeight k • F k)=A)
    (x y : Fin r → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock basis (complexify C *ᵥ x))
      (natFourWordBlock basis (complexify C *ᵥ y))=
      star x ⬝ᵥ (complexify A *ᵥ y) := by
  rw [natFourOriginalCOMForm_eq_sum_degree d _ _ (hN y) (hd y),← hA,
    natFour_complexify_sum,Matrix.sum_mulVec,dotProduct_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [natFourOriginalCOMTerm,hF k (Finset.mem_range.mp hk) x y,complexify_smul_rat]
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

#print axioms natFour_COM_source_matrix_form_explicit
end TorusLean.BosonFiniteCertificate
