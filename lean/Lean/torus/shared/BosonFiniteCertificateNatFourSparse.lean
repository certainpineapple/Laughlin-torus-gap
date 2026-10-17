import torus.shared.BosonFiniteCertificateNatFourGram

/-! A proved sparse evaluator of the original row-Gram form. It tests genuine
annihilator zeros before evaluating large coefficients. The source operator is
unchanged, and the sparse expression is a theorem-derived evaluator of it. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

def natFourTermsFormSparse (terms : List NatFourNormalTerm) (s u : List ℕ) : ℚ :=
  (terms.map fun term =>
    if wordRemovalWeight u term.annihilators = 0 then 0 else
      term.coefficient * natFourNormalWordForm s u term.creators term.annihilators).sum

theorem natFourTermsFormSparse_eq (terms : List NatFourNormalTerm) (s u : List ℕ) :
    natFourTermsFormSparse terms s u = natFourTermsForm terms s u := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro term ht
  by_cases h : wordRemovalWeight u term.annihilators = 0
  · simp [h, natFourNormalWordForm]
  · simp [h]

def natFourUnitColumnFormSparse (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) : ℚ :=
  natFourTermsFormSparse (natFourColumnPairTerms t (left,1) (right,1)) s u

theorem natFourUnitColumnFormSparse_eq (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) :
    natFourUnitColumnFormSparse t left right s u = natFourUnitColumnForm t left right s u :=
  natFourTermsFormSparse_eq _ s u

/-- The original column Gram is evaluated only when the actual differential
word and its occupation cross-form have a nonzero coefficient. -/
def natFourSparseChannelGramForm (t : ℕ) (s u : List ℕ) : ℚ :=
  ((natFourColumnSlots t).map fun i => ((natFourColumnSlots t).map fun j =>
    let F := natFourUnitColumnFormSparse t
      (natFourSourceColumn t i) (natFourSourceColumn t j) s u
    if F = 0 then 0 else (natFourOriginalColumnGram t i j : ℚ) * F).sum).sum

theorem natFourSparseChannelGramForm_eq (t : ℕ) (s u : List ℕ) :
    natFourSparseChannelGramForm t s u = natFourChannelGramForm t s u := by
  unfold natFourSparseChannelGramForm natFourChannelGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  dsimp only
  rw [natFourUnitColumnFormSparse_eq]
  by_cases h : natFourUnitColumnForm t (natFourSourceColumn t i) (natFourSourceColumn t j) s u = 0
  · simp [h]
  · simp [h]

def natFourSparseOriginalGramForm (s u : List ℕ) : ℚ :=
  ((List.range 4).map fun t => natFourSparseChannelGramForm t s u).sum

theorem natFourSparseOriginalGramForm_eq (s u : List ℕ) :
    natFourSparseOriginalGramForm s u = natFourOriginalGramForm s u := by
  unfold natFourSparseOriginalGramForm natFourOriginalGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact natFourSparseChannelGramForm_eq t s u

theorem canonicalNatFourOriginalOperator_sparse_form (s u : List ℕ) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourOriginalOperator (scaledWord factorialRootNat u)) =
      (natFourSparseOriginalGramForm s u : ℂ) := by
  rw [natFourSparseOriginalGramForm_eq, canonicalNatFourOriginalOperator_gram_form]

#print axioms natFourTermsFormSparse_eq
#print axioms natFourUnitColumnFormSparse_eq
#print axioms natFourSparseChannelGramForm_eq
#print axioms natFourSparseOriginalGramForm_eq
#print axioms canonicalNatFourOriginalOperator_sparse_form
end TorusLean.BosonFiniteCertificate
