import torus.shared.BosonFiniteCertificateNatFourS4Stability
import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatPairNormalizedRank

/-! A source-derived degree-shell amplitude factorization avoids repeatedly
evaluating all lower-degree pair removals. Every amplitude is still checked
against the true complete-removal word action before matrix algebra is used. -/
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

def natFourS4DegreeWordForm (d : ℕ) (s u : List ℕ) : ℚ :=
  ∑ p : Fin (d+1), natFourPairWeight p.val (d-p.val)*
    (natFourDoublePairRemoval p.val (d-p.val) s : ℚ)*
    (natFourDoublePairRemoval p.val (d-p.val) u : ℚ)

theorem canonicalNatFourS4_degree_word_form (d : ℕ) (s u : List ℕ)
    (hs : s.length=4) (hu : u.length=4) (hdu : u.sum=d) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourS4 (scaledWord factorialRootNat u))=
      (natFourS4DegreeWordForm d s u : ℂ) := by
  have hN : (scaledWord factorialRootNat u).IsHomogeneous 4 := by
    rw [scaledWordNat_monomial]
    exact MvPolynomial.isHomogeneous_monomial _ ((wordOccupation_degree_nat u).trans hu)
  have hd : (scaledWord factorialRootNat u).IsWeightedHomogeneous id d := by
    rw [← hdu]
    exact natFour_scaledWord_weighted u
  rw [canonicalNatFourS4_eq_shell_four d _ hN hd,canonicalNatFourS4Shell_form,
    nat_pair_list_range_sum,← Fin.sum_univ_eq_sum_range]
  simp only [natFourS4DegreeWordForm,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,
    canonicalNatFourDoublePair_word_form _ _ s u hs hu,mul_assoc]

def natFourS4AmplitudeGram {n : ℕ} (d : ℕ)
    (A : Matrix (Fin (d+1)) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Aᵀ*(Matrix.diagonal (fun p : Fin (d+1) => natFourPairWeight p.val (d-p.val))*A)

theorem natFourS4AmplitudeGram_apply {n : ℕ} (d : ℕ)
    (A : Matrix (Fin (d+1)) (Fin n) ℚ) (a b : Fin n) :
    natFourS4AmplitudeGram d A a b=
      ∑ p : Fin (d+1), natFourPairWeight p.val (d-p.val)*A p a*A p b := by
  rw [natFourS4AmplitudeGram,Matrix.mul_apply]
  simp only [Matrix.diagonal_mul,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem canonicalNatFourS4_amplitude_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (hsum : ∀ a, (basis a).sum=d)
    (A : Matrix (Fin (d+1)) (Fin n) ℚ)
    (hA : ∀ p a, (natFourDoublePairRemoval p.val (d-p.val) (basis a) : ℚ)=A p a)
    (S : Matrix (Fin n) (Fin n) ℚ) (hS : natFourS4AmplitudeGram d A=S)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourS4 (natFourWordBlock basis y))=
      star x ⬝ᵥ (complexify S *ᵥ y) := by
  apply natFourWordBlock_operator_matrix_form basis canonicalNatFourS4 S _ x y
  intro a b
  rw [canonicalNatFourS4_degree_word_form d _ _ (hlen a) (hlen b) (hsum b),← hS]
  congr 1
  simp only [natFourS4DegreeWordForm,hA,natFourS4AmplitudeGram_apply]

#print axioms canonicalNatFourS4_degree_word_form
#print axioms natFourS4AmplitudeGram_apply
#print axioms canonicalNatFourS4_amplitude_matrix_form
end TorusLean.BosonFiniteCertificate
