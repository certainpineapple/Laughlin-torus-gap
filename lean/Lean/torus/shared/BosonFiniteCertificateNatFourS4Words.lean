import Mathlib.Data.Rat.BigOperators
import torus.shared.BosonFiniteCertificateNatFourS4Core
import torus.shared.BosonFiniteCertificateNatFourSupport

/-! Actual double-pair action on genuine four-particle words and its exact
rational cross-form. Both repeated-particle multiplicities and the original
pair normalization remain explicit. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateRescaleCCR

private theorem natFourS4_list_flatMap_sum {ι A : Type*} [AddCommMonoid A]
    (l : List ι) (F : ι → List A) :
    (l.flatMap F).sum = (l.map fun a => (F a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

private theorem natFourS4_list_sum_smul (l : List ℂ) (f : Core ℕ ℂ) :
    l.sum • f = (l.map fun c => c • f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.sum_cons,add_smul,ih,List.map_cons]

def natFourDoublePairTerms (p q : ℕ) : List NatFourNormalTerm :=
  (List.range (p+1)).flatMap fun a => (List.range (q+1)).map fun b =>
    ⟨1,[],[a,p-a,b,q-b]⟩

theorem natFour_empty_four_comp (a b c d : ℕ) :
    normalWord (K := ℂ) [] [a,b,c,d] =
      (normalWord [] [c,d]).comp (normalWord [] [a,b]) := by
  apply LinearMap.ext
  intro f
  simp only [normalWord,wordPolynomial_nil,annihilateWord,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,LinearMap.id_apply,one_mul]

theorem paperNatFourDoublePair_source (p q : ℕ) :
    paperNatFourTerms (natFourDoublePairTerms p q) =
      (paperColumnWordOperator (K := ℂ) q none).comp (paperColumnWordOperator p none) := by
  apply LinearMap.ext
  intro f
  simp only [paperNatFourTerms,natFourDoublePairTerms,List.map_flatMap,List.map_map,
    Function.comp_def,Rat.cast_one,one_smul,natFourS4_list_flatMap_sum,
    nat_linear_list_sum_apply,paperColumnWordOperator,LinearMap.comp_apply,map_list_sum]
  simp only [natFour_empty_four_comp,LinearMap.comp_apply]

theorem canonicalNatFourDoublePair_source (p q : ℕ) :
    canonicalNatFourDoublePair p q = canonicalNatFourTerms (natFourDoublePairTerms p q) := by
  rw [canonicalNatFourTerms_conjugate,paperNatFourDoublePair_source,
    conjugateOperator_comp,← canonicalPairNat_eq_conjugate,← canonicalPairNat_eq_conjugate]
  rfl

/-- The finite integer amplitude of complete double-pair removal. -/
def natFourDoublePairRemoval (p q : ℕ) (s : List ℕ) : ℕ :=
  ((List.range (p+1)).map fun a => ((List.range (q+1)).map fun b =>
    wordRemovalWeight s [a,p-a,b,q-b]).sum).sum

theorem canonicalNatFour_full_removal (s labels : List ℕ)
    (hs : s.length=4) (hl : labels.length=4) :
    canonicalNatFourNormalWord [] labels (scaledWord factorialRootNat s) =
      (wordRemovalWeight s labels : ℂ) • (1 : Core ℕ ℂ) := by
  rw [canonicalNatFourNormalWord_action]
  by_cases hz : wordRemovalWeight s labels=0
  · simp [hz]
  · have hh := eraseWord_length_add s labels hz
    have he : eraseWord s labels=[] := List.eq_nil_of_length_eq_zero (by omega)
    simp [he,scaledWord,wordScale,wordPolynomial]

theorem canonicalNatFourDoublePair_word (p q : ℕ) (s : List ℕ) (hs : s.length=4) :
    canonicalNatFourDoublePair p q (scaledWord factorialRootNat s) =
      (natFourDoublePairRemoval p q s : ℂ) • (1 : Core ℕ ℂ) := by
  have hh (a b : ℕ) := canonicalNatFour_full_removal s [a,p-a,b,q-b] hs rfl
  rw [canonicalNatFourDoublePair_source]
  simp only [canonicalNatFourTerms,natFourDoublePairTerms,List.map_flatMap,List.map_map,
    Function.comp_def,Rat.cast_one,one_smul,natFourS4_list_flatMap_sum,nat_linear_list_sum_apply]
  simp only [List.map_map,Function.comp_def,hh]
  simp only [natFourDoublePairRemoval,Nat.cast_list_sum,List.map_map,Function.comp_def,
    natFourS4_list_sum_smul]

theorem natFour_vacuum_inner : natOccupationInner (1 : Core ℕ ℂ) 1=1 := by
  have h := natFour_scaledWord_inner [] []
  simpa [scaledWord,wordScale,wordPolynomial,natFourWordMetric,natFourOrbitalMetric,
    wordOccupation,natOccupationWeight] using h

theorem canonicalNatFourDoublePair_word_form (p q : ℕ) (s u : List ℕ)
    (hs : s.length=4) (hu : u.length=4) :
    natOccupationInner (canonicalNatFourDoublePair p q (scaledWord factorialRootNat s))
      (canonicalNatFourDoublePair p q (scaledWord factorialRootNat u)) =
      (natFourDoublePairRemoval p q s : ℂ)*(natFourDoublePairRemoval p q u : ℂ) := by
  rw [canonicalNatFourDoublePair_word p q s hs,canonicalNatFourDoublePair_word p q u hu,
    natOccupationInner_smul_left,natOccupationInner_smul_right,natFour_vacuum_inner]
  simp

def natFourS4WordForm (D : ℕ) (s u : List ℕ) : ℚ :=
  ((natFourPairSlots D).map fun pq => natFourPairWeight pq.1 pq.2 *
    (natFourDoublePairRemoval pq.1 pq.2 s : ℚ)*(natFourDoublePairRemoval pq.1 pq.2 u : ℚ)).sum

theorem canonicalNatFourS4_word_form (D : ℕ) (s u : List ℕ)
    (hs : s.length=4) (hu : u.length=4) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourS4Cutoff D (scaledWord factorialRootNat u)) =
      (natFourS4WordForm D s u : ℂ) := by
  rw [canonicalNatFourS4Cutoff_form]
  simp only [natFourS4WordForm,Rat.cast_list_sum,List.map_map,Function.comp_def,Rat.cast_mul,
    Rat.cast_natCast,canonicalNatFourDoublePair_word_form _ _ s u hs hu,mul_assoc]

#print axioms natFour_empty_four_comp
#print axioms paperNatFourDoublePair_source
#print axioms canonicalNatFourDoublePair_source
#print axioms canonicalNatFour_full_removal
#print axioms canonicalNatFourDoublePair_word
#print axioms natFour_vacuum_inner
#print axioms canonicalNatFourDoublePair_word_form
#print axioms canonicalNatFourS4_word_form
end TorusLean.BosonFiniteCertificate
