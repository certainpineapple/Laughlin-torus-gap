import torus.shared.BosonFiniteCertificateNatFourHWords
import torus.shared.BosonFiniteCertificateNatFourS4Words
import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateCanonicalGram
import torus.shared.BosonFiniteCertificateCanonicalFormsCore

/-! Matrix transport for the genuine independently defined pair Hamiltonian
and double-pair source. All numerical matrix identities remain proof inputs. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open Matrix
open scoped BigOperators

theorem natFourWordBlock_operator_matrix_form {n : ℕ}
    (basis : Fin n → List ℕ) (O : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ)
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ a b, natOccupationInner (scaledWord factorialRootNat (basis a))
      (O (scaledWord factorialRootNat (basis b)))=(M a b : ℂ))
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x) (O (natFourWordBlock basis y))=
      star x ⬝ᵥ (complexify M *ᵥ y) := by
  classical
  unfold natFourWordBlock
  rw [map_sum,natOccupationInner_sum_left]
  simp only [dotProduct,mulVec,complexify,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [natOccupationInner_smul_left,natOccupationInner_sum_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul,natOccupationInner_smul_right,hM a b]
  change star (x a) * (y b * (M a b : ℂ)) =
    star (x a) * ((M a b : ℂ) * y b)
  ring

theorem canonicalNatFourH_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hsum : ∀ a, (basis a).sum=d)
    (H : Matrix (Fin n) (Fin n) ℚ)
    (hH : ∀ a b, natFourHWordForm d (basis a) (basis b)=H a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock basis y))=
      star x ⬝ᵥ (complexify H *ᵥ y) := by
  apply natFourWordBlock_operator_matrix_form basis canonicalPairHamiltonianNat H _ x y
  intro a b
  rw [canonicalNatFourH_word_form,hsum b,hH a b]

theorem canonicalNatFourS4_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (hsum : ∀ a, (basis a).sum=d)
    (S : Matrix (Fin n) (Fin n) ℚ)
    (hS : ∀ a b, natFourS4WordForm d (basis a) (basis b)=S a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourS4 (natFourWordBlock basis y))=
      star x ⬝ᵥ (complexify S *ᵥ y) := by
  apply natFourWordBlock_operator_matrix_form basis canonicalNatFourS4 S _ x y
  intro a b
  have hw : (scaledWord factorialRootNat (basis b)).IsWeightedHomogeneous id d := by
    rw [← hsum b]
    exact natFour_scaledWord_weighted (basis b)
  rw [canonicalNatFourS4_eq_cutoff_weighted d _ hw,
    canonicalNatFourS4_word_form d _ _ (hlen a) (hlen b),hS a b]

theorem natFour_operator_relative_matrix_form {n r : ℕ}
    (basis : Fin n → List ℕ) (U : Matrix (Fin n) (Fin r) ℚ)
    (O : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ)
    (M : Matrix (Fin n) (Fin n) ℚ) (F : Matrix (Fin r) (Fin r) ℚ)
    (hM : ∀ x y, natOccupationInner (natFourWordBlock basis x)
      (O (natFourWordBlock basis y))=star x ⬝ᵥ (complexify M *ᵥ y))
    (hF : Uᵀ*M*U=F) (x y : Fin r → ℂ) :
    natOccupationInner (natFourWordBlock basis (complexify U *ᵥ x))
      (O (natFourWordBlock basis (complexify U *ᵥ y)))=
      star x ⬝ᵥ (complexify F *ᵥ y) := by
  rw [hM,matrixCross_congruence,← complexify_transpose_rect,
    ← complexify_mul_rect,← complexify_mul_rect,hF]

#print axioms natFourWordBlock_operator_matrix_form
#print axioms canonicalNatFourH_matrix_form
#print axioms canonicalNatFourS4_matrix_form
#print axioms natFour_operator_relative_matrix_form
end TorusLean.BosonFiniteCertificate
