import torus.shared.BosonFiniteCertificateNatCOMTail
import Mathlib.Data.Rat.BigOperators
import torus.shared.BosonFiniteCertificateNatFourComputable
import torus.shared.BosonFiniteCertificateNatPairHamiltonianAdjoint

/-! Rational word cross-forms of the independent genuine all-Nat Hamiltonian.
This is a finite coefficient restriction, not a new Hamiltonian or H4 rank
formula. The frozen canonicalPairHamiltonianNat remains the only source. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateAction

theorem natFour_canonicalPair_word (p : ℕ) (s : List ℕ) :
    canonicalPairNat p (scaledWord factorialRootNat s) =
      ((List.range (p+1)).map fun a => (wordRemovalWeight s [a,p-a] : ℂ) •
        scaledWord factorialRootNat (eraseWord s [a,p-a])).sum := by
  rw [canonicalPairNat_eq_conjugate,← rescaleEquiv_word factorialRootNat factorialRootNat_ne_zero,
    conjugateOperator_apply_rescale,paperColumnWordOperator,nat_linear_list_sum_apply,
    map_list_sum]
  simp only [List.map_map,Function.comp_def,normalWord_wordPolynomial,List.nil_append,
    map_smul,rescaleEquiv_word]

def natFourPairWordForm (p : ℕ) (s u : List ℕ) : ℚ :=
  ((List.range (p+1)).map fun a => ((List.range (p+1)).map fun b =>
    if (eraseWord s [a,p-a]).Perm (eraseWord u [b,p-b]) then
      (wordRemovalWeight s [a,p-a] : ℚ)*(natFourComputableMetric (eraseWord s [a,p-a]) : ℚ)*
        (wordRemovalWeight u [b,p-b] : ℚ) else 0).sum).sum

theorem natFour_canonicalPair_word_form (p : ℕ) (s u : List ℕ) :
    natOccupationInner (canonicalPairNat p (scaledWord factorialRootNat s))
      (canonicalPairNat p (scaledWord factorialRootNat u)) = (natFourPairWordForm p s u : ℂ) := by
  rw [natFour_canonicalPair_word,natFour_canonicalPair_word,natOccupationInner_list_sum_left]
  simp only [natFourPairWordForm,Rat.cast_list_sum,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [natOccupationInner_smul_left,natOccupationInner_list_sum_right,← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  rw [natOccupationInner_smul_right,natFour_scaledWord_inner]
  by_cases h : (eraseWord s [a,p-a]).Perm (eraseWord u [b,p-b])
  · simp [h,natFourOccupation_eq_iff_perm,natFourComputableMetric_eq,
      mul_comm,mul_left_comm,mul_assoc]
  · simp [h,natFourOccupation_eq_iff_perm]


def natFourHWordForm (D : ℕ) (s u : List ℕ) : ℚ :=
  ((List.range (D+1)).map fun p => ((p.factorial : ℚ)/2^(p+1))*natFourPairWordForm p s u).sum

theorem canonicalNatFourH_cutoff_word_form (D : ℕ) (s u : List ℕ) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalPairHamiltonianNatCutoff D (scaledWord factorialRootNat u)) =
      (natFourHWordForm D s u : ℂ) := by
  rw [canonicalPairHamiltonianNatCutoff_form]
  simp only [natFourHWordForm,Rat.cast_list_sum,List.map_map,Function.comp_def,Rat.cast_mul,
    Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast,natFour_canonicalPair_word_form]

theorem natFour_scaledWord_weighted (u : List ℕ) :
    (scaledWord factorialRootNat u).IsWeightedHomogeneous id u.sum := by
  rw [scaledWordNat_monomial]
  exact MvPolynomial.isWeightedHomogeneous_monomial id (wordOccupation u) _
    (wordOccupation_weight_nat u)

theorem canonicalNatFourH_word_form (s u : List ℕ) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalPairHamiltonianNat (scaledWord factorialRootNat u)) =
      (natFourHWordForm u.sum s u : ℂ) := by
  rw [canonicalPairHamiltonianNat_eq_cutoff_weighted u.sum _ (natFour_scaledWord_weighted u),
    canonicalNatFourH_cutoff_word_form]

#print axioms natFour_canonicalPair_word
#print axioms natFour_canonicalPair_word_form
#print axioms canonicalNatFourH_cutoff_word_form
#print axioms natFour_scaledWord_weighted
#print axioms canonicalNatFourH_word_form
end TorusLean.BosonFiniteCertificate
