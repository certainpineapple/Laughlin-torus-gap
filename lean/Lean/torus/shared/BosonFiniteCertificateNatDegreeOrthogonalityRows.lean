import torus.shared.BosonFiniteCertificateNatDegreeOrthogonality

/-! Actual degree separation for the original natural-label row operators.
Their one-particle outputs have degree d-t, and the operators really vanish
when d<t. This resolves the natural-subtraction boundary before using
orthogonality. Neither a block-diagonal form nor an M3 kernel is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

private theorem nat_degree_list_sum_zero {A B : Type*} [AddMonoid B]
    (s : List A) (f : A → B) (h : ∀ a ∈ s, f a = 0) : (s.map f).sum = 0 := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [List.map_cons, List.sum_cons, h a (by simp), zero_add]
    exact ih (fun b hb => h b (by simp [hb]))

theorem nat_wordRemovalWeight_zero_of_sum_lt (s labels : List ℕ)
    (h : s.sum < labels.sum) : wordRemovalWeight s labels = 0 := by
  by_contra hn
  have hs := eraseWord_sum_add s labels hn
  omega

theorem nat_columns_spectator_bounds (t p j : ℕ) (h : some (p,j) ∈ columns t) :
    t ≤ p+j ∧ p+j ≤ 8 := by
  have hc : some (p,j) ∈ ((List.range 9).filter (t ≤ ·)).flatMap
      (fun d => (List.range (d+1)).map (fun a => some (a,d-a))) := by
    simpa only [columns, List.mem_cons, Option.some_ne_none, false_or] using h
  rcases List.mem_flatMap.mp hc with ⟨d, hd, hp⟩
  rcases List.mem_map.mp hp with ⟨a, ha, hea⟩
  have hpair : a=p ∧ d-a=j := by
    simpa only [Option.some.injEq, Prod.mk.injEq] using hea
  have had : a ≤ d := Nat.le_of_lt_succ (List.mem_range.mp ha)
  have htd : t ≤ d := by simpa using (List.mem_filter.mp hd).2
  have hd9 : d < 9 := List.mem_range.mp (List.mem_filter.mp hd).1
  omega

/-- Three annihilations leave no spectator before the stated creator acts. -/
theorem nat_spectatorColumnOutputOK (t p j d : ℕ) (s : List ℕ)
    (hN : s.length=3) (hd : s.sum=d) : columnOutputOK t d s (some (p,j)) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hap : a ≤ p := Nat.le_of_lt_succ (List.mem_range.mp ha)
  change decide (removalWeight s [j,a,p-a]=0 ∨
    [p+j-t] ++ eraseWord s [j,a,p-a]=[d-t])=true
  simp only [decide_eq_true_eq]
  by_cases hz : removalWeight s [j,a,p-a]=0
  · exact Or.inl hz
  · right
    have hw : wordRemovalWeight s [j,a,p-a] ≠ 0 := by
      simpa only [removalWeight_eq_wordRemovalWeight] using hz
    have hl := eraseWord_length_add s [j,a,p-a] hw
    have hs := eraseWord_sum_add s [j,a,p-a] hw
    have hempty : eraseWord s [j,a,p-a]=[] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_cons, List.length_nil] at hl
      omega)
    simp only [hempty, List.sum_nil, List.sum_cons, Nat.add_zero, zero_add] at hs
    have hd' : p+j=d := by omega
    simp only [hempty, List.append_nil, hd']

theorem nat_rowOutputOK_of_length_sum (t d : ℕ) (s : List ℕ)
    (hN : s.length=3) (hd : s.sum=d) : rowOutputOK t d s = true := by
  apply List.all_eq_true.mpr
  intro col _
  cases col with
  | none => exact pairColumnOutputOK_of_length_sum t d s hN hd
  | some pj => exact nat_spectatorColumnOutputOK t pj.1 pj.2 d s hN hd

/-- The actual source row has no output below its removal degree. -/
theorem nat_paperRowWordOperator_low_degree_zero (t : ℕ) (row : List ℤ)
    (s : List ℕ) (h : s.sum < t) :
    paperRowWordOperator t row (wordPolynomial s : Core ℕ ℂ) = 0 := by
  have hc (col : Option (ℕ × ℕ)) (hcol : col ∈ columns t) :
      paperColumnWordOperator t col (wordPolynomial s : Core ℕ ℂ) = 0 := by
    cases col with
    | none =>
      rw [paperColumnWordOperator, nat_linear_list_sum_apply]
      apply nat_degree_list_sum_zero
      intro a ha
      have hat : a ≤ t := Nat.le_of_lt_succ (List.mem_range.mp ha)
      have hz : wordRemovalWeight s [a,t-a]=0 := nat_wordRemovalWeight_zero_of_sum_lt s _ (by
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
        omega)
      rw [normalWord_wordPolynomial, hz, Nat.cast_zero, zero_smul]
    | some pj =>
      have hbound := (nat_columns_spectator_bounds t pj.1 pj.2 hcol).1
      rw [paperColumnWordOperator, nat_linear_list_sum_apply]
      apply nat_degree_list_sum_zero
      intro a ha
      have hap : a ≤ pj.1 := Nat.le_of_lt_succ (List.mem_range.mp ha)
      have hz : wordRemovalWeight s [pj.2,a,pj.1-a]=0 := nat_wordRemovalWeight_zero_of_sum_lt s _ (by
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
        omega)
      rw [normalWord_wordPolynomial, hz, Nat.cast_zero, zero_smul]
  rw [paperRowWordOperator, nat_linear_list_sum_apply]
  apply nat_degree_list_sum_zero
  intro term ht
  rw [LinearMap.smul_apply, hc term.1 (List.of_mem_zip ht).1, smul_zero]

theorem canonicalNatRow_word_action (t d : ℕ) (row : List ℤ) (s : List ℕ)
    (hN : s.length=3) (hd : s.sum=d) :
    canonicalNatRow t row (scaledWord factorialRootNat s) =
      ((threeRowAction t row s : ℂ)/1000000000000) • scaledWord factorialRootNat [d-t] := by
  rw [canonicalNatRow, ←rescaleEquiv_word factorialRootNat factorialRootNat_ne_zero,
    conjugateOperator_apply_rescale,
    paperRowWordOperator_apply t d row s (nat_rowOutputOK_of_length_sum t d s hN hd), map_smul]
  have hx : (MvPolynomial.X (d-t) : Core ℕ ℂ) = wordPolynomial [d-t] := by simp [wordPolynomial]
  rw [hx, rescaleEquiv_word]

theorem canonicalNatRow_low_degree_zero (t d : ℕ) (row : List ℤ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) (hdt : d<t) :
    canonicalNatRow t row f = 0 := by
  have hspan : threeWordDegreeSpanNat d ≤ LinearMap.ker (canonicalNatRow t row) := by
    apply Submodule.span_le.mpr
    rintro f ⟨s, hlen, hsum, rfl⟩
    change canonicalNatRow t row (scaledWord factorialRootNat s)=0
    rw [canonicalNatRow, ←rescaleEquiv_word factorialRootNat factorialRootNat_ne_zero,
      conjugateOperator_apply_rescale,
      nat_paperRowWordOperator_low_degree_zero t row s (by omega), map_zero]
  exact hspan (homogeneous_mem_threeWordDegreeSpanNat d f hN hd)

/-- Actual N3 row outputs lie in the one-particle degree-(d-t) line. -/
theorem canonicalNatRow_singleton_output (t d : ℕ) (row : List ℤ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    canonicalNatRow t row f =
      natOccupationInner (MvPolynomial.X (d-t)) (canonicalNatRow t row f) • MvPolynomial.X (d-t) := by
  have hf := homogeneous_mem_threeWordDegreeSpanNat d f hN hd
  clear hN hd
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, hlen, hsum, rfl⟩ := hf
    rw [canonicalNatRow_word_action t d row s hlen hsum]
    simp only [scaledWord, wordScale, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, wordPolynomial, natOccupationInner_smul_right,
      natOccupationInner_X_self, smul_smul]
  | zero => simp only [map_zero, natOccupationInner_zero_right, zero_smul]
  | add f g hf hg ihf ihg =>
    simpa only [map_add, natOccupationInner_add_right, add_smul] using congrArg₂ (·+·) ihf ihg
  | smul c f hf ih =>
    simpa only [map_smul, natOccupationInner_smul_right, smul_smul] using congrArg (fun z => c • z) ih

theorem canonicalNatRow_cross_weight_zero (t d e : ℕ) (row : List ℤ)
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (he : g.IsWeightedHomogeneous id e) (hde : d≠e) :
    natOccupationInner (canonicalNatRow t row f) (canonicalNatRow t row g) = 0 := by
  by_cases hdt : d<t
  · rw [canonicalNatRow_low_degree_zero t d row f hNf hd hdt, natOccupationInner_zero_left]
  by_cases het : e<t
  · rw [canonicalNatRow_low_degree_zero t e row g hNg he het, natOccupationInner_zero_right]
  have hsub : d-t ≠ e-t := by omega
  have hz : natOccupationInner (MvPolynomial.X (d-t) : Core ℕ ℂ) (MvPolynomial.X (e-t))=0 :=
    natOccupationInner_eq_zero_of_weight_ne (d-t) (e-t) _ _
      (MvPolynomial.isWeightedHomogeneous_X ℂ id _) (MvPolynomial.isWeightedHomogeneous_X ℂ id _) hsub
  rw [canonicalNatRow_singleton_output t d row f hNf hd,
    canonicalNatRow_singleton_output t e row g hNg he]
  simp only [natOccupationInner_smul_left, natOccupationInner_smul_right, hz, mul_zero]

theorem canonicalNatOriginalM3Form_cross_weight_zero (d e : ℕ)
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (he : g.IsWeightedHomogeneous id e) (hde : d≠e) :
    canonicalNatOriginalM3Form f g = 0 := by
  unfold canonicalNatOriginalM3Form canonicalNatRowChannelForm
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro i _
  rw [canonicalNatRow_cross_weight_zero t.val d e _ f g hNf hd hNg he hde,
    canonicalNatRow_cross_weight_zero t.val d e _ f g hNf hd hNg he hde, sub_self]

theorem canonicalNatOriginalCOMTerm_cross_weight_zero (d e n : ℕ)
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (he : g.IsWeightedHomogeneous id e) (hde : d≠e) :
    canonicalNatOriginalCOMTerm f g n = 0 := by
  have hf := canonicalCOMRaiseNat_iterate_bihomogeneous d n f hNf hd
  have hg := canonicalCOMRaiseNat_iterate_bihomogeneous e n g hNg he
  rw [canonicalNatOriginalCOMTerm,
    canonicalNatOriginalM3Form_cross_weight_zero (d+n) (e+n) _ _ hf.1 hf.2 hg.1 hg.2 (by omega), mul_zero]

theorem canonicalNatOriginalCOMForm_cross_weight_zero (d e : ℕ)
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (he : g.IsWeightedHomogeneous id e) (hde : d≠e) :
    canonicalNatOriginalCOMForm f g = 0 := by
  unfold canonicalNatOriginalCOMForm
  simp only [canonicalNatOriginalCOMTerm_cross_weight_zero d e _ f g hNf hd hNg he hde, tsum_zero]

theorem canonicalNatInfiniteComparisonForm_relative_cross_weight_zero (d e : ℕ)
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (he : g.IsWeightedHomogeneous id e)
    (hLg : canonicalCOMLowerNat g=0) (hde : d≠e) :
    canonicalNatInfiniteComparisonForm f g = 0 := by
  unfold canonicalNatInfiniteComparisonForm
  rw [canonicalPairHamiltonianNat_relative_square_cross_weight_zero d e f g hd hNg he hLg hde,
    canonicalPairHamiltonianNat_relative_cross_weight_zero d e f g hd hNg he hLg hde,
    canonicalNatOriginalCOMForm_cross_weight_zero d e f g hNf hd hNg he hde]
  ring

#print axioms canonicalNatRow_low_degree_zero
#print axioms canonicalNatRow_singleton_output
#print axioms canonicalNatOriginalM3Form_cross_weight_zero
#print axioms canonicalNatOriginalCOMForm_cross_weight_zero
#print axioms canonicalNatInfiniteComparisonForm_relative_cross_weight_zero
end TorusLean.BosonFiniteCertificate
