import torus.shared.BosonFiniteCertificateConjugationFinite

/-! Genuine pair annihilation for every degree p ≤ 8, including the planar-H
range p=4,…,8 which is not covered by the four frozen row channels. The output
shape below is proved from particle number and total degree, not a data table. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Boson
open TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.BosonFiniteCertificate

variable {K : Type*} [Field K]

private theorem member_le_list_sum (s : List ℕ) (j : ℕ) (hj : j ∈ s) : j ≤ s.sum := by
  induction s with
  | nil => simp at hj
  | cons a s ih =>
    simp only [List.mem_cons] at hj
    simp only [List.sum_cons]
    rcases hj with h | h
    · subst j
      omega
    · have hi := ih h
      omega

/-- A total orbital degree below 9 already bounds every source label. -/
theorem sourceLabelsBounded9_of_sum_lt (s : List ℕ) (h : s.sum < 9) :
    sourceLabelsBounded9 s = true := by
  apply List.all_eq_true.mpr
  intro j hj
  apply decide_eq_true
  exact lt_of_le_of_lt (member_le_list_sum s j hj) h

/-- Successful annihilations remove exactly one particle per label. -/
theorem eraseWord_length_add (s labels : List ℕ)
    (h : wordRemovalWeight s labels ≠ 0) :
    (eraseWord s labels).length + labels.length = s.length := by
  induction labels generalizing s with
  | nil => simp [eraseWord]
  | cons j js ih =>
    have hh : s.count j ≠ 0 ∧ wordRemovalWeight (s.erase j) js ≠ 0 :=
      mul_ne_zero_iff.mp h
    have hm : j ∈ s := List.count_pos_iff.mp (Nat.pos_of_ne_zero hh.1)
    have hi := ih (s.erase j) hh.2
    have he := List.length_erase_add_one hm
    simp only [eraseWord, List.length_cons]
    omega

/-- Successful annihilations remove exactly the sum of the requested labels. -/
theorem eraseWord_sum_add (s labels : List ℕ)
    (h : wordRemovalWeight s labels ≠ 0) :
    (eraseWord s labels).sum + labels.sum = s.sum := by
  induction labels generalizing s with
  | nil => simp [eraseWord]
  | cons j js ih =>
    have hh : s.count j ≠ 0 ∧ wordRemovalWeight (s.erase j) js ≠ 0 :=
      mul_ne_zero_iff.mp h
    have hm : j ∈ s := List.count_pos_iff.mp (Nat.pos_of_ne_zero hh.1)
    have hi := ih (s.erase j) hh.2
    have he := List.sum_erase hm
    simp only [eraseWord, List.sum_cons]
    omega

/-- For every three-particle degree-d input, a pair of total degree p has
exactly the required singleton output whenever its coefficient is nonzero. -/
theorem pairColumnOutputOK_of_length_sum (p d : ℕ) (s : List ℕ)
    (hlen : s.length = 3) (hsum : s.sum = d) :
    columnOutputOK p d s none = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hale : a ≤ p := Nat.le_of_lt_succ (List.mem_range.mp ha)
  change decide (removalWeight s [a,p-a] = 0 ∨
    [] ++ eraseWord s [a,p-a] = [d-p]) = true
  simp only [decide_eq_true_eq]
  by_cases hz : removalWeight s [a,p-a] = 0
  · exact Or.inl hz
  · right
    have hw : wordRemovalWeight s [a,p-a] ≠ 0 := by
      simpa only [removalWeight_eq_wordRemovalWeight] using hz
    have hl := eraseWord_length_add s [a,p-a] hw
    have hs := eraseWord_sum_add s [a,p-a] hw
    have he : (eraseWord s [a,p-a]).length = 1 := by
      simp only [List.length_cons, List.length_nil] at hl
      omega
    obtain ⟨b,hb⟩ := List.length_eq_one_iff.mp he
    rw [hb] at hs
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs
    have hbd : b = d-p := by omega
    simp [hb,hbd]

theorem pairColumnLabelsBounded9 (p : ℕ) (hp : p < 9) :
    columnLabelsBounded9 p none = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hale : a ≤ p := Nat.le_of_lt_succ (List.mem_range.mp ha)
  simp only [wordLabelsBounded9, sourceLabelsBounded9, List.nil_append,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

theorem finitePaperColumn9_word_action (p d : ℕ) (s : List ℕ)
    (hs : sourceLabelsBounded9 s = true) (hout : d-p < 9)
    (hb : columnLabelsBounded9 p none = true)
    (ha : columnOutputOK p d s none = true) :
    finitePaperColumn9 p none (wordPolynomial (s.map fin9) : Core (Fin 9) K) =
      (pairRemoval s p : K) • MvPolynomial.X (fin9 (d-p)) := by
  apply MvPolynomial.rename_injective Fin.val Fin.val_injective
  rw [rename_finitePaperColumn9 p none hb, rename_fin9_word s hs,
    paperColumnWordOperator_apply p d s none ha, map_smul, MvPolynomial.rename_X]
  simp only [columnRemoval, fin9, Nat.mod_eq_of_lt hout]

theorem conjugated_finitePair9_action (κ : Fin 9 → K) (hκ : ∀ j, κ j ≠ 0)
    (p d : ℕ) (s : List ℕ) (hs : sourceLabelsBounded9 s = true)
    (hp : p < 9) (hd : d < 9) (hlen : s.length = 3) (hsum : s.sum = d) :
    conjugateOperator κ hκ (finitePaperColumn9 p none) (scaledWord κ (s.map fin9)) =
      (pairRemoval s p : K) • scaledWord κ [fin9 (d-p)] := by
  have hout : d-p < 9 := lt_of_le_of_lt (Nat.sub_le d p) hd
  rw [← rescaleEquiv_word κ hκ, conjugateOperator_apply_rescale,
    finitePaperColumn9_word_action p d s hs hout (pairColumnLabelsBounded9 p hp)
      (pairColumnOutputOK_of_length_sum p d s hlen hsum), map_smul]
  have hw : (MvPolynomial.X (fin9 (d-p)) : Core (Fin 9) K) =
      wordPolynomial [fin9 (d-p)] := by simp [wordPolynomial]
  rw [hw, rescaleEquiv_word]

/-- The explicit physical orbital factorial scale. -/
def pairFactorialRoot9 (j : Fin 9) : ℂ := (Real.sqrt (j.val.factorial : ℝ) : ℂ)

theorem pairFactorialRoot9_ne_zero (j : Fin 9) : pairFactorialRoot9 j ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.factorial_pos j.val))

/-- The full finite-variable differential operator, with no particle cutoff. -/
def canonicalPair9 (p : ℕ) : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ :=
  conjugateOperator pairFactorialRoot9 pairFactorialRoot9_ne_zero
    (finitePaperColumn9 p none)

theorem pair_scaledWord_canonical (s : List (Fin 9)) :
    scaledWord pairFactorialRoot9 s =
      canonicalMonomial (factorialScale 8) (wordOccupation s) :=
  scaledWord_eq_canonicalMonomial (factorialScale 8) s

theorem canonicalPair9_word_action (p d : ℕ) (s : List ℕ)
    (hs : sourceLabelsBounded9 s = true) (hp : p < 9) (hd : d < 9)
    (hlen : s.length = 3) (hsum : s.sum = d) :
    canonicalPair9 p (scaledWord pairFactorialRoot9 (s.map fin9)) =
      (pairRemoval s p : ℂ) • scaledWord pairFactorialRoot9 [fin9 (d-p)] :=
  conjugated_finitePair9_action pairFactorialRoot9 pairFactorialRoot9_ne_zero
    p d s hs hp hd hlen hsum

/-- The actual canonical cross form contains exactly the surviving orbital
factorial; repeated-mode falling factorials are retained by pairRemoval. -/
theorem canonicalPair9_word_form (p d : ℕ) (s q : List ℕ)
    (hs : sourceLabelsBounded9 s = true) (hq : sourceLabelsBounded9 q = true)
    (hp : p < 9) (hd : d < 9) (hls : s.length = 3) (hlq : q.length = 3)
    (hss : s.sum = d) (hsq : q.sum = d) :
    ip (canonicalPair9 p (scaledWord pairFactorialRoot9 (s.map fin9)))
      (canonicalPair9 p (scaledWord pairFactorialRoot9 (q.map fin9))) =
      ((d-p).factorial : ℂ) * (pairRemoval s p : ℂ) * (pairRemoval q p : ℂ) := by
  rw [canonicalPair9_word_action p d s hs hp hd hls hss,
    canonicalPair9_word_action p d q hq hp hd hlq hsq,
    TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right, pair_scaledWord_canonical,
    canonicalMonomial_inner]
  have hout : d-p < 9 := lt_of_le_of_lt (Nat.sub_le d p) hd
  simp [wordOccupation, occupationMetricWeight_single, factorialScale,
    fin9, Nat.mod_eq_of_lt hout, mul_comm, mul_left_comm, mul_assoc]

private theorem rat_list_sum_cast {I : Type*} (l : List I) (f : I → ℚ) :
    (((l.map f).sum : ℚ) : ℂ) = (l.map fun a => (f a : ℂ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The frozen planar H form is a weighted sum of genuine pair-removal cross
forms on all three-particle degree-d words. No H action table is assumed. -/
theorem planarHForm_eq_canonicalPair_forms (d : ℕ) (s q : List ℕ)
    (hs : sourceLabelsBounded9 s = true) (hq : sourceLabelsBounded9 q = true)
    (hd : d < 9) (hls : s.length = 3) (hlq : q.length = 3)
    (hss : s.sum = d) (hsq : q.sum = d) :
    (planarHForm d s q : ℂ) =
      ((List.range (d+1)).map fun p =>
        ((p.factorial : ℂ) / (2 : ℂ)^(p+1)) *
          ip (canonicalPair9 p (scaledWord pairFactorialRoot9 (s.map fin9)))
            (canonicalPair9 p (scaledWord pairFactorialRoot9 (q.map fin9)))).sum := by
  rw [planarHForm, rat_list_sum_cast]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hp9 : p < 9 := lt_of_le_of_lt (Nat.le_of_lt_succ (List.mem_range.mp hp)) hd
  rw [canonicalPair9_word_form p d s q hs hq hp9 hd hls hlq hss hsq]
  push_cast
  ring

#print axioms sourceLabelsBounded9_of_sum_lt
#print axioms pairColumnOutputOK_of_length_sum
#print axioms conjugated_finitePair9_action
#print axioms canonicalPair9_word_form
#print axioms planarHForm_eq_canonicalPair_forms
end TorusLean.Shared.BosonFiniteCertificateConjugation
