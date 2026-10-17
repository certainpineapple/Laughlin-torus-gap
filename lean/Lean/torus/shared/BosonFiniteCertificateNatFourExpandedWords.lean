import torus.shared.BosonFiniteCertificateNatFourRationalWords

/-! Finite word-list certificates for the actual COM action. Natural
coefficients are expanded as repeated words, and sorting only uses the
commutativity of the original polynomial variables. Thus a computable list
permutation check replaces a large symbolic polynomial expansion. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

def natFourSortedWord (s : List ℕ) : List ℕ := s.mergeSort (fun a b => a ≤ b)

def natFourExpandedWords (l : List (ℕ × List ℕ)) : List (List ℕ) :=
  l.flatMap fun cw => List.replicate cw.1 (natFourSortedWord cw.2)

theorem natFour_wordPolynomial_perm (s u : List ℕ) (h : s.Perm u) :
    (wordPolynomial s : Core ℕ ℚ)=wordPolynomial u :=
  (h.map (fun j => (MvPolynomial.X j : Core ℕ ℚ))).prod_eq

theorem natFour_wordPolynomial_sorted (s : List ℕ) :
    (wordPolynomial (natFourSortedWord s) : Core ℕ ℚ)=wordPolynomial s :=
  natFour_wordPolynomial_perm _ _ (List.mergeSort_perm _ _)

theorem natFourExpandedWords_form (l : List (ℕ × List ℕ)) :
    ((natFourExpandedWords l).map fun s => (wordPolynomial s : Core ℕ ℚ)).sum=
      (l.map fun cw => (cw.1 : ℚ) • (wordPolynomial cw.2 : Core ℕ ℚ)).sum := by
  induction l with
  | nil => rfl
  | cons cw l ih =>
    simp only [natFourExpandedWords,List.flatMap_cons,List.map_append,List.sum_append,
      List.map_replicate,List.sum_replicate,natFour_wordPolynomial_sorted,
      List.map_cons,List.sum_cons,Nat.cast_smul_eq_nsmul] at ih ⊢
    rw [ih]

theorem natFourExpandedWords_basis_form {m : ℕ} (dst : Fin m → List ℕ) (c : Fin m → ℕ) :
    ((natFourExpandedWords (List.ofFn fun b => (c b,dst b))).map
      fun s => (wordPolynomial s : Core ℕ ℚ)).sum=
      ∑ b, (c b : ℚ) • (wordPolynomial (dst b) : Core ℕ ℚ) := by
  rw [natFourExpandedWords_form]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]

theorem natFour_lower_rational_of_expanded_perm {m : ℕ} (s : List ℕ)
    (dst : Fin m → List ℕ) (c : Fin m → ℕ)
    (h : (natFourExpandedWords (natFourLoweredWords s)).Perm
      (natFourExpandedWords (List.ofFn fun b => (c b,dst b)))) :
    natFourRationalLowerWord s=∑ b, (c b : ℚ) • (wordPolynomial (dst b) : Core ℕ ℚ) := by
  have hp := (h.map (fun w => (wordPolynomial w : Core ℕ ℚ))).sum_eq
  rw [natFourExpandedWords_form,natFourExpandedWords_basis_form] at hp
  exact hp

theorem natFour_raise_rational_of_expanded_perm {m : ℕ} (s : List ℕ)
    (dst : Fin m → List ℕ) (c : Fin m → ℕ)
    (h : (natFourExpandedWords ((raisedWordsNat s).map fun w => (1,w))).Perm
      (natFourExpandedWords (List.ofFn fun b => (c b,dst b)))) :
    natFourRationalRaiseWord s=∑ b, (c b : ℚ) • (wordPolynomial (dst b) : Core ℕ ℚ) := by
  have hp := (h.map (fun w => (wordPolynomial w : Core ℕ ℚ))).sum_eq
  rw [natFourExpandedWords_form,natFourExpandedWords_basis_form] at hp
  simpa only [List.map_map,Function.comp_def,Nat.cast_one,one_smul,
    natFourRationalRaiseWord] using hp

#print axioms natFour_wordPolynomial_perm
#print axioms natFour_wordPolynomial_sorted
#print axioms natFourExpandedWords_form
#print axioms natFourExpandedWords_basis_form
#print axioms natFour_lower_rational_of_expanded_perm
#print axioms natFour_raise_rational_of_expanded_perm
end TorusLean.BosonFiniteCertificate
