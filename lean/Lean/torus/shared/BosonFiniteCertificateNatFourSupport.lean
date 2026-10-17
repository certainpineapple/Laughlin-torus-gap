import torus.shared.BosonFiniteCertificateNatFourRows
import torus.shared.BosonFiniteCertificateConjugationPair

/-! Source support of the original four-body normal tensor. These proofs read
the frozen column convention, not a target finite matrix. They establish true
one-sided annihilation on four-particle words of orbital degree above sixteen.
No claim that the displayed word span exhausts a homogeneous sector is made.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

/-- Both bounds are read before the natural subtraction i=p+j-t is used. -/
theorem natFour_columns_spectator_bound (t p j : ℕ)
    (h : some (p,j) ∈ columns t) : t ≤ p+j ∧ p+j ≤ 8 := by
  change some (p,j) ∈ none :: ((List.range 9).filter (t ≤ ·)).flatMap
    (fun d => (List.range (d+1)).map (fun q => some (q,d-q))) at h
  simp only [List.mem_cons, Option.some_ne_none, false_or] at h
  rcases List.mem_flatMap.mp h with ⟨d, hd, hq⟩
  rcases List.mem_map.mp hq with ⟨q, hq, he⟩
  have hqp : q = p := congrArg Prod.fst (Option.some.inj he)
  have hdj : d-q = j := congrArg Prod.snd (Option.some.inj he)
  have hd8 : d < 9 := List.mem_range.mp (List.mem_filter.mp hd).1
  have htd : t ≤ d := of_decide_eq_true (List.mem_filter.mp hd).2
  have hqd : q ≤ d := Nat.le_of_lt_succ (List.mem_range.mp hq)
  omega

theorem natFourOriginalTerm_shape (t p j p' j' a b : ℕ) (c c' : ℤ)
    (ht : t ≤ p+j) (ht' : t ≤ p'+j') (hpj : p+j ≤ 8) (hpj' : p'+j' ≤ 8)
    (ha : a ≤ p) (hb : b ≤ p') :
    let term := natFourOriginalTerm t p j p' j' a b c c'
    term.creators.length = 4 ∧ term.annihilators.length = 4 ∧
      term.creators.sum = term.annihilators.sum ∧ term.annihilators.sum ≤ 16 := by
  change 4 = 4 ∧ 4 = 4 ∧
    a + ((p-a) + (j + ((p'+j'-t) + 0))) =
      (p+j-t) + (j' + (b + ((p'-b) + 0))) ∧
    (p+j-t) + (j' + (b + ((p'-b) + 0))) ≤ 16
  omega

/-- Every actual original term has four creators, four annihilators, preserves
orbital degree, and has annihilator orbital degree at most sixteen. -/
theorem natFourOriginalRowTerms_shape (t : ℕ) (row : List ℤ)
    (term : NatFourNormalTerm) (h : term ∈ natFourOriginalRowTerms t row) :
    term.creators.length = 4 ∧ term.annihilators.length = 4 ∧
      term.creators.sum = term.annihilators.sum ∧ term.annihilators.sum ≤ 16 := by
  rcases List.mem_flatMap.mp h with ⟨left, hl, h⟩
  rcases List.mem_flatMap.mp h with ⟨right, hr, h⟩
  rcases left with ⟨left,c⟩
  rcases right with ⟨right,c'⟩
  cases left with
  | none => simp [natFourColumnPairTerms] at h
  | some left =>
    rcases left with ⟨p,j⟩
    cases right with
    | none => simp [natFourColumnPairTerms] at h
    | some right =>
      rcases right with ⟨p',j'⟩
      have hp := natFour_columns_spectator_bound t p j (List.of_mem_zip hl).1
      have hp' := natFour_columns_spectator_bound t p' j' (List.of_mem_zip hr).1
      rcases List.mem_flatMap.mp h with ⟨a,ha,h⟩
      rcases List.mem_map.mp h with ⟨b,hb,rfl⟩
      exact natFourOriginalTerm_shape t p j p' j' a b c c'
        hp.1 hp'.1 hp.2 hp'.2 (Nat.le_of_lt_succ (List.mem_range.mp ha))
        (Nat.le_of_lt_succ (List.mem_range.mp hb))

theorem natFourOriginalTerms_shape (term : NatFourNormalTerm)
    (h : term ∈ natFourOriginalTerms) :
    term.creators.length = 4 ∧ term.annihilators.length = 4 ∧
      term.creators.sum = term.annihilators.sum ∧ term.annihilators.sum ≤ 16 := by
  rcases List.mem_flatMap.mp h with ⟨entry, _, ht⟩
  exact natFourOriginalRowTerms_shape entry.1 entry.2 term ht

/-- Equal particle counts force successful full annihilation to remove exactly
the source orbital degree, including repeated labels. -/
theorem natFour_removal_high_degree_zero (s labels : List ℕ)
    (hs : s.length = 4) (hl : labels.length = 4) (hd : 16 < s.sum)
    (hlabels : labels.sum ≤ 16) : wordRemovalWeight s labels = 0 := by
  by_contra h
  have hlen := eraseWord_length_add s labels h
  have hsum := eraseWord_sum_add s labels h
  have hnil : eraseWord s labels = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [hnil, List.sum_nil, zero_add] at hsum
  omega

private theorem natFour_terms_annihilate (terms : List NatFourNormalTerm) (s : List ℕ)
    (h : ∀ term ∈ terms, canonicalNatFourNormalWord term.creators term.annihilators
      (scaledWord factorialRootNat s) = 0) :
    canonicalNatFourTerms terms (scaledWord factorialRootNat s) = 0 := by
  induction terms with
  | nil => simp [canonicalNatFourTerms]
  | cons term terms ih =>
    simp only [canonicalNatFourTerms, List.map_cons, List.sum_cons,
      LinearMap.add_apply, LinearMap.smul_apply] at ih ⊢
    rw [h term (by simp), smul_zero, zero_add]
    exact ih (fun b hb => h b (by simp [hb]))

/-- Genuine one-sided operator tail, on every arbitrary Nat-label four-word. -/
theorem canonicalNatFourOriginalOperator_word_tail (s : List ℕ)
    (hs : s.length = 4) (hd : 16 < s.sum) :
    canonicalNatFourOriginalOperator (scaledWord factorialRootNat s) = 0 := by
  apply natFour_terms_annihilate
  intro term ht
  have shape := natFourOriginalTerms_shape term ht
  rw [canonicalNatFourNormalWord_action,
    natFour_removal_high_degree_zero s term.annihilators hs shape.2.1 hd shape.2.2.2,
    Nat.cast_zero, zero_smul]

def natFourHighDegreeWordSpan : Submodule ℂ (Core ℕ ℂ) :=
  Submodule.span ℂ {f | ∃ s : List ℕ, s.length = 4 ∧ 16 < s.sum ∧
    f = scaledWord factorialRootNat s}

theorem canonicalNatFourOriginalOperator_tail_span :
    natFourHighDegreeWordSpan ≤ LinearMap.ker canonicalNatFourOriginalOperator := by
  apply Submodule.span_le.mpr
  rintro f ⟨s,hs,hd,rfl⟩
  exact canonicalNatFourOriginalOperator_word_tail s hs hd

#print axioms natFour_columns_spectator_bound
#print axioms natFourOriginalTerm_shape
#print axioms natFourOriginalRowTerms_shape
#print axioms natFourOriginalTerms_shape
#print axioms natFour_removal_high_degree_zero
#print axioms canonicalNatFourOriginalOperator_word_tail
#print axioms canonicalNatFourOriginalOperator_tail_span
end TorusLean.BosonFiniteCertificate
