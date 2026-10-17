import torus.shared.BosonFiniteCertificateCanonicalFormsCore
import torus.shared.BosonFiniteCertificateConjugationPair

/-! The frozen spectator columns annihilate exactly three particles whose
labels sum to at most eight. On a three-particle source word of total degree
above eight every such column is zero. The actual row is consequently its
original pure-pair first column, so the actual M3 row-square subtraction
vanishes on the span of those source words. This is only the M3 tail identity;
no claim about S, H, arbitrary particle sectors, or torus thermal tails is made. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open scoped BigOperators
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateConjugation

/-- Equal particle counts leave no particle after successful full annihilation,
so the removed label sum must equal the source label sum. -/
theorem m3_removalWeight_zero_of_degree_ne (s labels : List ℕ)
    (hlen : s.length = labels.length) (hdeg : s.sum ≠ labels.sum) :
    wordRemovalWeight s labels = 0 := by
  by_contra hn
  have hl := eraseWord_length_add s labels hn
  have hs := eraseWord_sum_add s labels hn
  have hz : (eraseWord s labels).length = 0 := by omega
  have he : eraseWord s labels = [] := List.eq_nil_of_length_eq_zero hz
  simp only [he, List.sum_nil, zero_add] at hs
  exact hdeg hs.symm

/-- The source support bound is proved directly from the original column list,
independently of all row coefficients and without enumerating source degrees. -/
theorem m3_columns_tail_spectator_bound (t : ℕ) (col : Option (ℕ × ℕ))
    (hc : col ∈ (columns t).tail) : ∃ p j, col = some (p,j) ∧ p+j ≤ 8 := by
  change col ∈ ((List.range 9).filter (t ≤ ·)).flatMap
    (fun d => (List.range (d+1)).map (fun p => some (p,d-p))) at hc
  rcases List.mem_flatMap.mp hc with ⟨d, hd, hp⟩
  rcases List.mem_map.mp hp with ⟨p, hp, he⟩
  refine ⟨p, d-p, he.symm, ?_⟩
  have hd' : d < 9 := List.mem_range.mp (List.mem_filter.mp hd).1
  have hp' : p ≤ d := Nat.le_of_lt_succ (List.mem_range.mp hp)
  omega

private theorem m3_sum_map_zero {I A : Type*} [AddMonoid A] (l : List I) (f : I → A)
    (h : ∀ a ∈ l, f a = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, h a (by simp), zero_add]
    exact ih (fun b hb => h b (by simp [hb]))

private theorem m3_operator_list_zero {I K : Type*} [Field K] (l : List I)
    (ops : I → Core ℕ K →ₗ[K] Core ℕ K) (f : Core ℕ K)
    (h : ∀ a ∈ l, ops a f = 0) : (l.map ops).sum f = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, h a (by simp), zero_add]
    exact ih (fun b hb => h b (by simp [hb]))

theorem m3_spectator_removal_tail_zero (s : List ℕ) (p j : ℕ)
    (hlen : s.length = 3) (hdeg : 8 < s.sum) (hpj : p+j ≤ 8) :
    spectatorPairRemoval s p j = 0 := by
  apply m3_sum_map_zero
  intro a ha
  have ha' : a ≤ p := Nat.le_of_lt_succ (List.mem_range.mp ha)
  rw [removalWeight_eq_wordRemovalWeight]
  apply m3_removalWeight_zero_of_degree_ne
  · simpa using hlen
  · simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

/-- A genuine spectator differential column vanishes, even for Nat labels
above the finite oscillator cutoff. No output-shape hypothesis is needed. -/
theorem m3_paper_spectator_tail_zero {K : Type*} [Field K]
    (t p j : ℕ) (s : List ℕ) (hlen : s.length = 3)
    (hdeg : 8 < s.sum) (hpj : p+j ≤ 8) :
    paperColumnWordOperator t (some (p,j)) (wordPolynomial s : Core ℕ K) = 0 := by
  apply m3_operator_list_zero
  intro a ha
  have ha' : a ≤ p := Nat.le_of_lt_succ (List.mem_range.mp ha)
  have hw : wordRemovalWeight s [j,a,p-a] = 0 := by
    apply m3_removalWeight_zero_of_degree_ne
    · simpa using hlen
    · simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
  rw [normalWord_wordPolynomial, hw, Nat.cast_zero, zero_smul]

theorem m3_paper_row_tail_pair {K : Type*} [Field K] (t : ℕ) (row : List ℤ)
    (s : List ℕ) (hlen : s.length = 3) (hdeg : 8 < s.sum) :
    paperRowWordOperator t row (wordPolynomial s : Core ℕ K) =
      ((rowInteger row 0 : K) / 1000000000000) •
        paperColumnWordOperator (K := K) t none (wordPolynomial s : Core ℕ K) := by
  cases row with
  | nil => simp [paperRowWordOperator, rowInteger]
  | cons c row =>
    have hz : ((((columns t).tail.zip row).map fun (term : Option (ℕ × ℕ) × ℤ) =>
        ((term.2 : K) / 1000000000000) • paperColumnWordOperator (K := K) t term.1).sum)
          (wordPolynomial s : Core ℕ K) = 0 := by
      apply m3_operator_list_zero
      intro term ht
      rcases m3_columns_tail_spectator_bound t term.1 (List.of_mem_zip ht).1 with
        ⟨p,j,hcol,hpj⟩
      rw [LinearMap.smul_apply, hcol, m3_paper_spectator_tail_zero t p j s hlen hdeg hpj,
        smul_zero]
    change (((c : K) / 1000000000000) • paperColumnWordOperator (K := K) t none +
      (((columns t).tail.zip row).map fun (term : Option (ℕ × ℕ) × ℤ) =>
        ((term.2 : K) / 1000000000000) • paperColumnWordOperator (K := K) t term.1).sum)
        (wordPolynomial s : Core ℕ K) = _
    rw [LinearMap.add_apply, LinearMap.smul_apply, hz, add_zero]
    rfl

theorem m3_paper_row_tail_pure {K : Type*} [Field K] (t : ℕ) (row : List ℤ)
    (s : List ℕ) (hlen : s.length = 3) (hdeg : 8 < s.sum) :
    paperRowWordOperator t row (wordPolynomial s : Core ℕ K) =
      paperRowWordOperator t [rowInteger row 0] (wordPolynomial s) := by
  rw [m3_paper_row_tail_pair t row s hlen hdeg,
    m3_paper_row_tail_pair t [rowInteger row 0] s hlen hdeg]
  rfl

/-- The same true row identity survives any invertible diagonal change of variables. -/
theorem m3_conjugated_Nat_row_tail {K : Type*} [Field K]
    (κ : ℕ → K) (hκ : ∀ j, κ j ≠ 0) (t : ℕ) (row : List ℤ)
    (s : List ℕ) (hlen : s.length = 3) (hdeg : 8 < s.sum) :
    conjugateOperator κ hκ (paperRowWordOperator t row) (scaledWord κ s) =
      conjugateOperator κ hκ (paperRowWordOperator t [rowInteger row 0]) (scaledWord κ s) := by
  rw [← rescaleEquiv_word κ hκ, conjugateOperator_apply_rescale,
    conjugateOperator_apply_rescale, m3_paper_row_tail_pure t row s hlen hdeg]

/-- The original integer row coefficient itself has only its original pair term. -/
theorem m3_threeRowAction_tail_pair (t : ℕ) (row : List ℤ) (s : List ℕ)
    (hlen : s.length = 3) (hdeg : 8 < s.sum) :
    threeRowAction t row s = rowInteger row 0 * (pairRemoval s t : ℤ) := by
  rw [threeRowAction_eq_sum]
  cases row with
  | nil => simp [rowInteger]
  | cons c row =>
    have hz : (((columns t).tail.zip row).map fun term =>
        term.2 * (columnRemoval t s term.1 : ℤ)).sum = 0 := by
      apply m3_sum_map_zero
      intro term ht
      rcases m3_columns_tail_spectator_bound t term.1 (List.of_mem_zip ht).1 with
        ⟨p,j,hcol,hpj⟩
      rw [hcol]
      change term.2 * (spectatorPairRemoval s p j : ℤ) = 0
      rw [m3_spectator_removal_tail_zero s p j hlen hdeg hpj]
      simp
    change c * (pairRemoval s t : ℤ) +
      (((columns t).tail.zip row).map fun term =>
        term.2 * (columnRemoval t s term.1 : ℤ)).sum = _
    rw [hz, add_zero]
    rfl

theorem m3_threeRowCross_tail_zero (t : ℕ) (row : List ℤ) (s q : List ℕ)
    (hls : s.length = 3) (hlq : q.length = 3) (hds : 8 < s.sum) (hdq : 8 < q.sum) :
    threeRowAction t row s * threeRowAction t row q -
      rowInteger row 0 * rowInteger row 0 * (pairRemoval s t : ℤ) * (pairRemoval q t : ℤ) = 0 := by
  rw [m3_threeRowAction_tail_pair t row s hls hds,
    m3_threeRowAction_tail_pair t row q hlq hdq]
  ring

/-- The original rational M3 coefficient formula has an exact, unbounded
three-particle degree tail of zero; no numeric source cutoff is assumed. -/
theorem threeRowForm_tail_zero (d : ℕ) (s q : List ℕ)
    (hls : s.length = 3) (hlq : q.length = 3) (hds : 8 < s.sum) (hdq : 8 < q.sum) :
    threeRowForm d s q = 0 := by
  have hn : threeRowFormNumerator d s q = 0 := by
    apply m3_sum_map_zero
    intro t ht
    split_ifs
    · have hz : ((frozenRows t).map fun row =>
          threeRowAction t row s * threeRowAction t row q -
            rowInteger row 0 * rowInteger row 0 * (pairRemoval s t : ℤ) *
              (pairRemoval q t : ℤ)).sum = 0 := by
        apply m3_sum_map_zero
        intro row hr
        exact m3_threeRowCross_tail_zero t row s q hls hlq hds hdq
      rw [hz, mul_zero]
    · rfl
  simp [threeRowForm, hn]

theorem m3_finitePaperRow9_tail (t : Fin 4) (row : List ℤ) (s : List ℕ)
    (hs : sourceLabelsBounded9 s = true) (hlen : s.length = 3) (hdeg : 8 < s.sum) :
    finitePaperRow9 t.val row (wordPolynomial (s.map fin9) : Core (Fin 9) ℂ) =
      finitePaperRow9 t.val [rowInteger row 0] (wordPolynomial (s.map fin9)) := by
  apply MvPolynomial.rename_injective Fin.val Fin.val_injective
  rw [rename_finitePaperRow9 t.val row (frozen_rows_labels_bounded t),
    rename_finitePaperRow9 t.val [rowInteger row 0] (frozen_rows_labels_bounded t),
    rename_fin9_word s hs]
  exact m3_paper_row_tail_pure t.val row s hlen hdeg

private theorem m3_val_labels_bounded (w : List (Fin 9)) :
    sourceLabelsBounded9 (w.map Fin.val) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  rcases List.mem_map.mp hj with ⟨a, ha, rfl⟩
  exact decide_eq_true a.isLt

private theorem m3_fin9_val_word (w : List (Fin 9)) :
    (w.map Fin.val).map fin9 = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  apply List.map_congr_left
  intro a ha
  apply Fin.ext
  exact Nat.mod_eq_of_lt a.isLt

theorem m3_canonical_row_tail (t : Fin 4) (row : List ℤ) (w : List (Fin 9))
    (hlen : w.length = 3) (hdeg : 8 < (w.map Fin.val).sum) :
    canonicalFrozenRow9 t.val row (scaledWord factorialRoot9 w) =
      canonicalFrozenRow9 t.val [rowInteger row 0] (scaledWord factorialRoot9 w) := by
  have hp := m3_finitePaperRow9_tail t row (w.map Fin.val) (m3_val_labels_bounded w)
    (by simpa using hlen) hdeg
  rw [m3_fin9_val_word] at hp
  rw [canonicalFrozenRow9, canonicalFrozenRow9,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, conjugateOperator_apply_rescale, hp]

/-- The structural high-degree three-particle source space, not a target kernel assumption. -/
def m3TailSpan9 : Submodule ℂ (Core (Fin 9) ℂ) :=
  Submodule.span ℂ {f | ∃ w : List (Fin 9), w.length = 3 ∧
    8 < (w.map Fin.val).sum ∧ f = scaledWord factorialRoot9 w}

theorem m3_tail_span_row_difference_zero (t : Fin 4) (row : List ℤ) :
    m3TailSpan9 ≤ LinearMap.ker
      (canonicalFrozenRow9 t.val row - canonicalFrozenRow9 t.val [rowInteger row 0]) := by
  apply Submodule.span_le.mpr
  rintro f ⟨w, hlen, hdeg, rfl⟩
  change canonicalFrozenRow9 t.val row (scaledWord factorialRoot9 w) -
    canonicalFrozenRow9 t.val [rowInteger row 0] (scaledWord factorialRoot9 w) = 0
  exact sub_eq_zero.mpr (m3_canonical_row_tail t row w hlen hdeg)

theorem m3_canonical_row_tail_span (t : Fin 4) (row : List ℤ)
    (f : Core (Fin 9) ℂ) (hf : f ∈ m3TailSpan9) :
    canonicalFrozenRow9 t.val row f = canonicalFrozenRow9 t.val [rowInteger row 0] f := by
  have h := m3_tail_span_row_difference_zero t row hf
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using h

/-- The exact original 138-row M3 form vanishes on its high-degree source span.
Only the M3 row-square minus pure-pair-square restriction is asserted. -/
theorem canonicalOriginalM3Form_tail_span_zero (f g : Core (Fin 9) ℂ)
    (hf : f ∈ m3TailSpan9) (hg : g ∈ m3TailSpan9) :
    canonicalOriginalM3Form f g = 0 := by
  unfold canonicalOriginalM3Form canonicalRowChannelForm
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro i hi
  rw [m3_canonical_row_tail_span t _ f hf, m3_canonical_row_tail_span t _ g hg]
  exact sub_self _

#print axioms m3_removalWeight_zero_of_degree_ne
#print axioms m3_columns_tail_spectator_bound
#print axioms m3_spectator_removal_tail_zero
#print axioms m3_paper_spectator_tail_zero
#print axioms m3_paper_row_tail_pair
#print axioms m3_paper_row_tail_pure
#print axioms m3_conjugated_Nat_row_tail
#print axioms m3_threeRowAction_tail_pair
#print axioms m3_threeRowCross_tail_zero
#print axioms threeRowForm_tail_zero
#print axioms m3_finitePaperRow9_tail
#print axioms m3_canonical_row_tail
#print axioms m3_tail_span_row_difference_zero
#print axioms m3_canonical_row_tail_span
#print axioms canonicalOriginalM3Form_tail_span_zero
end TorusLean.BosonFiniteCertificate
