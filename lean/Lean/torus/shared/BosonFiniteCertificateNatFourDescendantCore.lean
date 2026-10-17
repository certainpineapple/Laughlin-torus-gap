import torus.shared.BosonFiniteCertificateNatFourBasisHomogeneous
import torus.shared.BosonFiniteCertificateNatFourCOMForm
import torus.shared.BosonFiniteCertificateCanonicalFormsCore
import torus.shared.BosonFiniteCertificateCanonicalCompressionCore

/-! Actual unbounded Nat COM descendants, represented only after genuine
raising actions have been proved. Rational coordinates and compressed forms
are verification inputs; neither determines the source raising or M4. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFour_descendant_step {r m n : ℕ} (k : ℕ)
    (source : (Fin r → ℂ) → Core ℕ ℂ)
    (prev : Fin n → List ℕ) (next : Fin m → List ℕ)
    (C : Matrix (Fin n) (Fin r) ℚ) (D : Matrix (Fin m) (Fin r) ℚ)
    (R : Matrix (Fin m) (Fin n) ℚ)
    (hprev : ∀ x, (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] (source x)=
      natFourWordBlock prev (complexify C *ᵥ x))
    (hR : ∀ v, canonicalCOMRaiseNat (natFourWordBlock prev v)=
      natFourWordBlock next (complexify R *ᵥ v))
    (hD : R*C=D) (x : Fin r → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k+1] (source x)=
      natFourWordBlock next (complexify D *ᵥ x) := by
  rw [Function.iterate_succ_apply',hprev x,hR,Matrix.mulVec_mulVec,
    ← complexify_mul_rect,hD]

theorem natFour_descendant_source_form {r n : ℕ} (k : ℕ)
    (source : (Fin r → ℂ) → Core ℕ ℂ) (basis : Fin n → List ℕ)
    (D : Matrix (Fin n) (Fin r) ℚ) (M : Matrix (Fin n) (Fin n) ℚ)
    (F : Matrix (Fin r) (Fin r) ℚ)
    (hD : ∀ x, (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] (source x)=
      natFourWordBlock basis (complexify D *ᵥ x))
    (hM : ∀ x y, natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y))=
      star x ⬝ᵥ (complexify M *ᵥ y))
    (hF : Dᵀ*M*D=F) (x y : Fin r → ℂ) :
    natOccupationInner ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] (source x))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] (source y)))=
      star x ⬝ᵥ (complexify F *ᵥ y) := by
  rw [hD x,hD y,hM,matrixCross_congruence,← complexify_transpose_rect,
    ← complexify_mul_rect,← complexify_mul_rect,hF]

theorem natFour_complexify_sum {ι : Type*} {r : ℕ} (s : Finset ι)
    (F : ι → Matrix (Fin r) (Fin r) ℚ) :
    complexify (∑ i ∈ s, F i)=∑ i ∈ s, complexify (F i) := by
  ext a b
  simp [complexify, Matrix.sum_apply]

theorem natFour_COM_source_matrix_form {r : ℕ} (d : ℕ)
    (source : (Fin r → ℂ) → Core ℕ ℂ)
    (hN : ∀ x, (source x).IsHomogeneous 4)
    (hd : ∀ x, (source x).IsWeightedHomogeneous id d)
    (F : ℕ → Matrix (Fin r) (Fin r) ℚ)
    (hF : ∀ k, k<17-d → ∀ x y,
      natOccupationInner ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] (source x))
        (canonicalNatFourOriginalOperator
          ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] (source y)))=
        star x ⬝ᵥ (complexify (F k) *ᵥ y))
    (A : Matrix (Fin r) (Fin r) ℚ)
    (hA : (∑ k ∈ Finset.range (17-d), natFourOriginalCOMWeight k • F k)=A)
    (x y : Fin r → ℂ) :
    natFourOriginalCOMForm (source x) (source y)=star x ⬝ᵥ (complexify A *ᵥ y) := by
  rw [natFourOriginalCOMForm_eq_sum_degree d _ _ (hN y) (hd y),← hA,
    natFour_complexify_sum,Matrix.sum_mulVec,dotProduct_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [natFourOriginalCOMTerm,hF k (Finset.mem_range.mp hk) x y,complexify_smul_rat]
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

#print axioms natFour_descendant_step
#print axioms natFour_descendant_source_form
#print axioms natFour_complexify_sum
#print axioms natFour_COM_source_matrix_form
end TorusLean.BosonFiniteCertificate
