import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatRelativeRankComparisonCore

/-! The genuine factorial Gram of arbitrary finite Nat occupation columns.
The family is made from the actual scaled words, independently of any source
matrix. Both inverse Gram factors are retained in every rank coefficient. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateRealization
open Matrix
open scoped BigOperators ComplexOrder

def natFourWordGram {n : ℕ} (basis : Fin n → List ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal fun a => (natFourWordMetric (basis a) : ℚ)

def natFourColumnFamily {n r : ℕ} (basis : Fin n → List ℕ)
    (U : Matrix (Fin n) (Fin r) ℚ) : Fin r → Core ℕ ℂ :=
  fun j => natFourWordBlock basis (fun a => complexify U a j)

theorem natFourWordBlock_gram_form {n : ℕ} (basis : Fin n → List ℕ)
    (hinj : Function.Injective (fun a => wordOccupation (basis a))) (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x) (natFourWordBlock basis y)=
      star x ⬝ᵥ (complexify (natFourWordGram basis) *ᵥ y) := by
  apply natFourWordBlock_operator_matrix_form basis (LinearMap.id : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ)
    (natFourWordGram basis) _ x y
  intro a b
  by_cases h : a=b
  · subst b
    simp only [LinearMap.id_apply,natFour_scaledWord_inner,ite_true,
      natFourWordGram,Matrix.diagonal_apply_eq,Rat.cast_natCast]
  · have ho : wordOccupation (basis a)≠wordOccupation (basis b) := fun he => h (hinj he)
    simp only [LinearMap.id_apply,natFour_scaledWord_inner,if_neg ho,
      natFourWordGram,Matrix.diagonal_apply_ne _ h,Rat.cast_zero]

theorem natFourColumnFamily_synthesis {n r : ℕ} (basis : Fin n → List ℕ)
    (U : Matrix (Fin n) (Fin r) ℚ) (x : Fin r → ℂ) :
    natFamilySynthesis (natFourColumnFamily basis U) x=
      natFourWordBlock basis (complexify U *ᵥ x) := by
  simp only [natFamilySynthesis,natFourColumnFamily,natFourWordBlock,
    Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec,dotProduct,Finset.sum_smul,mul_comm]

theorem natFourColumnFamily_gram {n r : ℕ} (basis : Fin n → List ℕ)
    (hinj : Function.Injective (fun a => wordOccupation (basis a)))
    (U : Matrix (Fin n) (Fin r) ℚ) :
    natFamilyGram (natFourColumnFamily basis U)=
      complexify (Uᵀ*natFourWordGram basis*U) := by
  rw [complexify_mul_rect,complexify_mul_rect,complexify_transpose_rect]
  ext i j
  change natOccupationInner (natFourWordBlock basis (fun a => complexify U a i))
    (natFourWordBlock basis (fun a => complexify U a j)) = _
  rw [natFourWordBlock_gram_form basis hinj,dotProduct_mulVec]
  rfl

/-- A diagonal multiplication is evaluated once per occupation, not by a
quadratic zero-filled matrix multiplication. This is an exact matrix identity. -/
theorem natFour_diagonal_compression_entry {n r : ℕ} (g : Fin n → ℚ)
    (U : Matrix (Fin n) (Fin r) ℚ) (i j : Fin r) :
    (Uᵀ*Matrix.diagonal g*U) i j = ∑ a, U a i*g a*U a j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply]

theorem natFourColumnFamily_inverseGram_form {n r : ℕ} (basis : Fin n → List ℕ)
    (hinj : Function.Injective (fun a => wordOccupation (basis a)))
    (U : Matrix (Fin n) (Fin r) ℚ) (F J E : Matrix (Fin r) (Fin r) ℚ)
    (hF : Uᵀ*natFourWordGram basis*U=F) (hFJ : F*J=1) (hJF : J*F=1)
    (x y : Fin r → ℂ) :
    natFamilyRankForm (natFourColumnFamily basis U)
      (inverseGramCoefficient (complexify J) (complexify E))
      (natFourWordBlock basis (complexify U *ᵥ x))
      (natFourWordBlock basis (complexify U *ᵥ y)) = star x ⬝ᵥ (complexify E *ᵥ y) := by
  rw [←natFourColumnFamily_synthesis,←natFourColumnFamily_synthesis]
  apply natFamilyRankForm_inverseGram _ (complexify F) (complexify J) (complexify E)
  · rw [natFourColumnFamily_gram basis hinj,hF]
  · rw [←complexify_mul_rect,hFJ,complexify_one_rat]
  · rw [←complexify_mul_rect,hJF,complexify_one_rat]

theorem natFour_inverseGramCoefficient_posSemidef {r : ℕ}
    (J : Matrix (Fin r) (Fin r) ℚ) (E : Matrix (Fin r) (Fin r) ℂ)
    (hJ : Jᵀ=J) (hE : E.PosSemidef) :
    (inverseGramCoefficient (complexify J) E).PosSemidef := by
  apply inverseGramCoefficient_posSemidef _ _ _ hE
  rw [Matrix.IsHermitian,←complexify_transpose_rect,hJ]

/-- Genuine relative completeness removes both coordinate premises. The
comparison form is an independent input; it is never defined by its matrix. -/
theorem natFour_relative_rank_form {n r : ℕ} (d : ℕ) (basis : Fin n → List ℕ)
    (hinj : Function.Injective (fun a => wordOccupation (basis a)))
    (U : Matrix (Fin n) (Fin r) ℚ) (F J E : Matrix (Fin r) (Fin r) ℚ)
    (hF : Uᵀ*natFourWordGram basis*U=F) (hFJ : F*J=1) (hJF : J*F=1)
    (sourceForm : Core ℕ ℂ → Core ℕ ℂ → ℂ)
    (hform : ∀ x y, sourceForm (natFourWordBlock basis (complexify U *ᵥ x))
      (natFourWordBlock basis (complexify U *ᵥ y))=star x ⬝ᵥ (complexify E *ᵥ y))
    (hfull : ∀ f : Core ℕ ℂ, f.IsHomogeneous 4 → f.IsWeightedHomogeneous id d →
      canonicalCOMLowerNat f=0 → ∃ x, natFourWordBlock basis (complexify U *ᵥ x)=f)
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 4) (hdf : f.IsWeightedHomogeneous id d)
    (hLf : canonicalCOMLowerNat f=0) (hNg : g.IsHomogeneous 4)
    (hdg : g.IsWeightedHomogeneous id d) (hLg : canonicalCOMLowerNat g=0) :
    natFamilyRankForm (natFourColumnFamily basis U)
      (inverseGramCoefficient (complexify J) (complexify E)) f g=sourceForm f g := by
  obtain ⟨x,rfl⟩ := hfull f hNf hdf hLf
  obtain ⟨y,rfl⟩ := hfull g hNg hdg hLg
  rw [natFourColumnFamily_inverseGram_form basis hinj U F J E hF hFJ hJF]
  exact (hform x y).symm

#print axioms natFourWordBlock_gram_form
#print axioms natFourColumnFamily_synthesis
#print axioms natFourColumnFamily_gram
#print axioms natFour_diagonal_compression_entry
#print axioms natFourColumnFamily_inverseGram_form
#print axioms natFour_inverseGramCoefficient_posSemidef
#print axioms natFour_relative_rank_form
end TorusLean.BosonFiniteCertificate
