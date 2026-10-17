import torus.shared.BosonFiniteCertificateNatFourActivePairsCore
import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! Finite matrix forms of an already independently defined original M4.
This file assumes a proved entry identity, never defines the source operator
from its matrix. Complete occupation sectors are supplied separately. -/
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

theorem canonicalNatFourOriginalOperator_matrix_form {n : ℕ}
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ a b, natFourComputableGramForm (basis a) (basis b)=M a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y)) =
      star x ⬝ᵥ (complexify M *ᵥ y) := by
  have he (a b : Fin n) : natFourOriginalWordForm (basis a) (basis b)=M a b :=
    (natFourOriginalWordForm_eq_gram _ _).trans
      ((natFourDegreeOriginalGramForm_eq _ _ (hlen b)).symm.trans
        ((natFourComputableGramForm_eq _ _).symm.trans (hM a b)))
  rw [canonicalNatFourOriginalOperator_block_form]
  simp only [he,dotProduct,mulVec,complexify,Finset.mul_sum,mul_assoc]
  rfl

theorem canonicalNatFourOriginalOperator_active_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (hsum : ∀ a, (basis a).sum=d)
    (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ a b, natFourActiveGramForm pairs (basis a) (basis b)=M a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y)) =
      star x ⬝ᵥ (complexify M *ᵥ y) := by
  apply canonicalNatFourOriginalOperator_matrix_form basis hlen M _ x y
  intro a b
  rw [← natFourIndexedGramForm_eq,← natFourActiveGramForm_eq d pairs hpairs _ _ (hsum b)]
  exact hM a b

#print axioms canonicalNatFourOriginalOperator_active_matrix_form
#print axioms canonicalNatFourOriginalOperator_matrix_form
end TorusLean.BosonFiniteCertificate
