import torus.shared.BosonFiniteCertificateNatFourPrefixSparse

/-! Two-sided source sparsity. A four-word form can be nonzero only when
both actual spectator prefixes can be removed. This improves evaluation of
large source blocks without introducing a target-dependent sparsity mask. -/
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

theorem natFour_removal_input_perm (s u labels : List ℕ) (h : s.Perm u) :
    wordRemovalWeight s labels=wordRemovalWeight u labels := by
  induction labels generalizing s u with
  | nil => rfl
  | cons j labels ih =>
    simp only [wordRemovalWeight,List.perm_iff_count.mp h j,
      ih (s.erase j) (u.erase j) (List.Perm.erase j h)]

theorem natFour_removal_self (s : List ℕ) :
    wordRemovalWeight s s=natFourMultiplicity s := by
  induction s with
  | nil => rfl
  | cons j s ih =>
    simp only [wordRemovalWeight,List.erase_cons_head,List.count_cons_self,
      natFourMultiplicity,ih]

theorem natFourNormalForm_output_prefix_zero (s u labels : List ℕ) (a b c d : ℕ)
    (hs : s.length=4) (hz : wordRemovalWeight s [c,d]=0) :
    natFourComputableNormalForm s u [a,b,c,d] labels=0 := by
  unfold natFourComputableNormalForm
  split
  · rename_i hp
    have hl := hp.length_eq
    have he : eraseWord u labels=[] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_append,List.length_cons,List.length_nil,hs] at hl
      omega)
    rw [he,List.append_nil] at hp
    have hp' : s.Perm ([c,d]++[a,b]) :=
      hp.trans (List.perm_append_comm (l₁ := [a,b]) (l₂ := [c,d]))
    have hfull := natFour_removal_prefix_zero s [c,d] [a,b] hz
    rw [natFour_removal_input_perm s _ _ hp',natFour_removal_self,
      natFourMultiplicity_eq_weight] at hfull
    exact (Nat.ne_of_gt (natOccupationWeight_pos (wordOccupation ([c,d]++[a,b]))) hfull).elim
  · rfl

theorem natFourComputableUnitForm_output_prefix_zero (t p j p' j' : ℕ) (s u : List ℕ)
    (hs : s.length=4) (h : wordRemovalWeight s [j,p'+j'-t]=0) :
    natFourComputableUnitForm t (some (p,j)) (some (p',j')) s u=0 := by
  change (if (p+j-t)+j'+p'=u.sum then
    natFourComputableTermsForm (natFourColumnPairTerms t (some (p,j),1) (some (p',j'),1)) s u
    else 0)=0
  split
  · unfold natFourComputableTermsForm
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨term,ht,rfl⟩ := List.mem_map.mp hz
    obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    have hh : natFourComputableNormalForm s u
        (natFourOriginalTerm t p j p' j' a b 1 1).creators
        (natFourOriginalTerm t p j p' j' a b 1 1).annihilators=0 :=
      natFourNormalForm_output_prefix_zero s u _ a (p-a) j (p'+j'-t) hs h
    rw [hh,mul_zero]
    split <;> rfl
  · rfl

def natFourDualPrefixUnitForm (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) : ℚ :=
  match left,right with
  | some (p,j),some (p',j') =>
      if wordRemovalWeight s [j,p'+j'-t]=0 then 0 else
        natFourPrefixUnitForm t left right s u
  | _,_ => 0

theorem natFourDualPrefixUnitForm_eq (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) (hs : s.length=4) :
    natFourDualPrefixUnitForm t left right s u=natFourComputableUnitForm t left right s u := by
  cases left with
  | none => cases right <;> rfl
  | some left =>
    rcases left with ⟨p,j⟩
    cases right with
    | none => rfl
    | some right =>
      rcases right with ⟨p',j'⟩
      change (if wordRemovalWeight s [j,p'+j'-t]=0 then 0 else
        natFourPrefixUnitForm t (some (p,j)) (some (p',j')) s u)=_
      split
      · rename_i h
        exact (natFourComputableUnitForm_output_prefix_zero t p j p' j' s u hs h).symm
      · exact natFourPrefixUnitForm_eq _ _ _ _ _

def natFourDualPrefixSourcePairContribution (t : ℕ) (s u : List ℕ)
    (pair : NatFourSourceColumnPair) : ℚ :=
  let F := natFourDualPrefixUnitForm t pair.1.1 pair.2.1 s u
  if F=0 then 0 else (natFourOriginalColumnGram t pair.1.2 pair.2.2 : ℚ)*F

def natFourDualPrefixGramForm (pairs : ℕ → List NatFourSourceColumnPair)
    (s u : List ℕ) : ℚ :=
  ((List.range 4).map fun t =>
    ((pairs t).map (natFourDualPrefixSourcePairContribution t s u)).sum).sum

theorem natFourDualPrefixGramForm_eq (pairs : ℕ → List NatFourSourceColumnPair)
    (s u : List ℕ) (hs : s.length=4) :
    natFourDualPrefixGramForm pairs s u=natFourActiveGramForm pairs s u := by
  unfold natFourDualPrefixGramForm natFourActiveGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair hp
  simp only [natFourDualPrefixSourcePairContribution,natFourSourcePairContribution,
    natFourDualPrefixUnitForm_eq _ _ _ s u hs]

theorem canonicalNatFourOriginalOperator_dual_prefix_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (hsum : ∀ a, (basis a).sum=d)
    (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ a b, natFourDualPrefixGramForm pairs (basis a) (basis b)=M a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y)) =
      star x ⬝ᵥ (complexify M *ᵥ y) := by
  apply canonicalNatFourOriginalOperator_active_matrix_form d basis hlen hsum pairs hpairs M _ x y
  intro a b
  rw [← natFourDualPrefixGramForm_eq _ _ _ (hlen a)]
  exact hM a b

#print axioms natFour_removal_input_perm
#print axioms natFour_removal_self
#print axioms natFourNormalForm_output_prefix_zero
#print axioms natFourComputableUnitForm_output_prefix_zero
#print axioms natFourDualPrefixUnitForm_eq
#print axioms natFourDualPrefixGramForm_eq
#print axioms canonicalNatFourOriginalOperator_dual_prefix_matrix_form
end TorusLean.BosonFiniteCertificate
