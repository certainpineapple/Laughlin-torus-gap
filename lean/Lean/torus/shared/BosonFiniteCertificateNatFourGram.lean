import torus.shared.BosonFiniteCertificateNatFourRows

/-! Exact aggregation of the original frozen row pairs into their column Gram.
This is an identity derived from the already defined original differential
operator. No Gram table or target M4 matrix is used to define that operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateConjugation

/-- Original column positions, retaining the pure-pair column at position 0. -/
def natFourColumnSlots (t : ℕ) : List ℕ := List.range (columns t).length

def natFourSourceColumn (t i : ℕ) : Option (ℕ × ℕ) := (columns t)[i]?.getD none

/-- A source-only finite check that position-indexing preserves every original
zipped column and coefficient, including zero and repeated rows. -/
def natFourIndexedZipCheck (t : ℕ) : Bool :=
  (frozenRows t).all fun row => decide ((columns t).zip row =
    (natFourColumnSlots t).map fun i => (natFourSourceColumn t i, rowInteger row i))

theorem natFourIndexedZipCheck_acceptance : ∀ t : Fin 4,
    natFourIndexedZipCheck t.val = true := by
  intro t
  fin_cases t <;> decide +kernel

theorem natFour_original_row_indexed (t : Fin 4) (row : List ℤ)
    (hr : row ∈ frozenRows t.val) :
    (columns t.val).zip row = (natFourColumnSlots t.val).map
      (fun i => (natFourSourceColumn t.val i, rowInteger row i)) :=
  of_decide_eq_true (List.all_eq_true.mp (natFourIndexedZipCheck_acceptance t) row hr)

theorem natFourTermsForm_append (A B : List NatFourNormalTerm) (s u : List ℕ) :
    natFourTermsForm (A ++ B) s u = natFourTermsForm A s u + natFourTermsForm B s u := by
  simp only [natFourTermsForm, List.map_append, List.sum_append]

theorem natFourTermsForm_flatMap {ι : Type*} (l : List ι)
    (f : ι → List NatFourNormalTerm) (s u : List ℕ) :
    natFourTermsForm (l.flatMap f) s u = (l.map fun i => natFourTermsForm (f i) s u).sum := by
  induction l with
  | nil => simp [natFourTermsForm]
  | cons a l ih =>
    rw [List.flatMap_cons, natFourTermsForm_append, ih]
    rfl

/-- Bilinearity of the literal physical factorial coefficient in the original
signed row entries. The factor 10^24 has not been discarded. -/
theorem natFourOriginalCoefficient_scale (t p j a : ℕ) (c c' : ℤ) :
    natFourOriginalCoefficient t p j a c c' =
      (c : ℚ) * (c' : ℚ) * natFourOriginalCoefficient t p j a 1 1 := by
  simp only [natFourOriginalCoefficient, natFourDecodedRowEntry, Int.cast_one]
  ring

def natFourUnitColumnForm (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) : ℚ :=
  natFourTermsForm (natFourColumnPairTerms t (left,1) (right,1)) s u

theorem natFourColumnPairTerms_form_scale (t : ℕ) (left right : Option (ℕ × ℕ))
    (c c' : ℤ) (s u : List ℕ) :
    natFourTermsForm (natFourColumnPairTerms t (left,c) (right,c')) s u =
      (c : ℚ) * (c' : ℚ) * natFourUnitColumnForm t left right s u := by
  cases left with
  | none => simp [natFourColumnPairTerms, natFourUnitColumnForm, natFourTermsForm]
  | some left =>
    rcases left with ⟨p,j⟩
    cases right with
    | none => simp [natFourColumnPairTerms, natFourUnitColumnForm, natFourTermsForm]
    | some right =>
      rcases right with ⟨p',j'⟩
      simp only [natFourUnitColumnForm, natFourColumnPairTerms]
      simp only [natFourTermsForm_flatMap]
      simp only [natFourTermsForm, List.map_map, Function.comp_def, natFourOriginalTerm]
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro a ha
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro b hb
      rw [natFourOriginalCoefficient_scale]
      ring

private theorem natFour_list_sum_swap {ι κ : Type*} (l : List ι) (m : List κ)
    (f : ι → κ → ℚ) :
    (l.map fun i => (m.map fun j => f i j).sum).sum =
      (m.map fun j => (l.map fun i => f i j).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.sum_map_add]

private theorem natFour_integer_sum_cast {ι : Type*} (l : List ι) (f : ι → ℤ) :
    (((l.map f).sum : ℤ) : ℚ) = (l.map fun i => (f i : ℚ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Gram entry calculated from the original frozen integer row at each index. -/
def natFourOriginalColumnGram (t i j : ℕ) : ℤ :=
  ((frozenRows t).map fun row => rowInteger row i * rowInteger row j).sum

def natFourChannelGramForm (t : ℕ) (s u : List ℕ) : ℚ :=
  ((natFourColumnSlots t).map fun i => ((natFourColumnSlots t).map fun j =>
    (natFourOriginalColumnGram t i j : ℚ) *
      natFourUnitColumnForm t (natFourSourceColumn t i) (natFourSourceColumn t j) s u).sum).sum

def natFourOriginalChannelForm (t : ℕ) (s u : List ℕ) : ℚ :=
  natFourTermsForm ((frozenRows t).flatMap fun row => natFourOriginalRowTerms t row) s u

theorem natFourOriginalRowTerms_form_indexed (t : Fin 4) (row : List ℤ)
    (hr : row ∈ frozenRows t.val) (s u : List ℕ) :
    natFourTermsForm (natFourOriginalRowTerms t.val row) s u =
      ((natFourColumnSlots t.val).map fun i => ((natFourColumnSlots t.val).map fun j =>
        (rowInteger row i : ℚ) * (rowInteger row j : ℚ) *
          natFourUnitColumnForm t.val (natFourSourceColumn t.val i)
            (natFourSourceColumn t.val j) s u).sum).sum := by
  unfold natFourOriginalRowTerms
  simp only [natFour_original_row_indexed t row hr,
    natFourTermsForm_flatMap, List.map_map, Function.comp_def,
    natFourColumnPairTerms_form_scale]

/-- Exact finite sum rearrangement: source row pairs become the source column
Gram, with every original coefficient and physical metric retained. -/
theorem natFourOriginalChannelForm_eq_gram (t : Fin 4) (s u : List ℕ) :
    natFourOriginalChannelForm t.val s u = natFourChannelGramForm t.val s u := by
  unfold natFourOriginalChannelForm
  rw [natFourTermsForm_flatMap]
  have hrow : ((frozenRows t.val).map fun row =>
      natFourTermsForm (natFourOriginalRowTerms t.val row) s u) =
    (frozenRows t.val).map (fun row =>
      ((natFourColumnSlots t.val).map fun i => ((natFourColumnSlots t.val).map fun j =>
        (rowInteger row i : ℚ) * (rowInteger row j : ℚ) *
          natFourUnitColumnForm t.val (natFourSourceColumn t.val i)
            (natFourSourceColumn t.val j) s u).sum).sum) := by
    apply List.map_congr_left
    intro row hr
    exact natFourOriginalRowTerms_form_indexed t row hr s u
  rw [hrow, natFour_list_sum_swap]
  unfold natFourChannelGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [natFour_list_sum_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  simp only [natFourOriginalColumnGram, natFour_integer_sum_cast, Int.cast_mul,
    List.sum_map_mul_right]

def natFourOriginalGramForm (s u : List ℕ) : ℚ :=
  ((List.range 4).map fun t => natFourChannelGramForm t s u).sum

theorem natFourOriginalWordForm_eq_channels (s u : List ℕ) :
    natFourOriginalWordForm s u =
      ((List.range 4).map fun t => natFourOriginalChannelForm t s u).sum := by
  simp only [natFourOriginalWordForm, natFourOriginalTerms, natFourOriginalRows,
    List.flatMap_assoc, List.flatMap_map, Function.comp_def,
    natFourTermsForm_flatMap, natFourOriginalChannelForm]

theorem natFourOriginalWordForm_eq_gram (s u : List ℕ) :
    natFourOriginalWordForm s u = natFourOriginalGramForm s u := by
  rw [natFourOriginalWordForm_eq_channels]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact natFourOriginalChannelForm_eq_gram ⟨t,List.mem_range.mp ht⟩ s u

theorem canonicalNatFourOriginalOperator_gram_form (s u : List ℕ) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourOriginalOperator (scaledWord factorialRootNat u)) =
      (natFourOriginalGramForm s u : ℂ) := by
  rw [canonicalNatFourOriginalOperator_word_form, natFourOriginalWordForm_eq_gram]

#print axioms natFourIndexedZipCheck_acceptance
#print axioms natFour_original_row_indexed
#print axioms natFourTermsForm_flatMap
#print axioms natFourOriginalCoefficient_scale
#print axioms natFourColumnPairTerms_form_scale
#print axioms natFourOriginalRowTerms_form_indexed
#print axioms natFourOriginalChannelForm_eq_gram
#print axioms natFourOriginalWordForm_eq_channels
#print axioms natFourOriginalWordForm_eq_gram
#print axioms canonicalNatFourOriginalOperator_gram_form
end TorusLean.BosonFiniteCertificate
