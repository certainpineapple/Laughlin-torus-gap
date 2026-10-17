import torus.shared.BosonFiniteCertificateNatFourMatrixCore

/-! A source-only early annihilator test. Both spectator labels must be
removed before either pair summation can contribute. Skipping a failed prefix
is proved from the original ordered falling factorial, independently of every
finite target matrix. -/
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

theorem natFour_removal_append (s first rest : List ℕ) :
    wordRemovalWeight s (first++rest)=
      wordRemovalWeight s first*wordRemovalWeight (eraseWord s first) rest := by
  induction first generalizing s with
  | nil => simp [wordRemovalWeight,eraseWord]
  | cons j first ih =>
    simp only [List.cons_append,wordRemovalWeight,eraseWord,ih,Nat.mul_assoc]

theorem natFour_removal_prefix_zero (s first rest : List ℕ)
    (h : wordRemovalWeight s first=0) :
    wordRemovalWeight s (first++rest)=0 := by
  rw [natFour_removal_append,h,zero_mul]

theorem natFourComputableUnitForm_prefix_zero (t p j p' j' : ℕ) (s u : List ℕ)
    (h : wordRemovalWeight u [p+j-t,j']=0) :
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
    have hz : wordRemovalWeight u
        (natFourOriginalTerm t p j p' j' a b 1 1).annihilators=0 := by
      simpa only [natFourOriginalTerm,List.cons_append,List.nil_append] using
        natFour_removal_prefix_zero u [p+j-t,j'] [b,p'-b] h
    simp only [hz,ite_true]
  · rfl

def natFourPrefixUnitForm (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) : ℚ :=
  match left,right with
  | some (p,j),some (p',j') =>
      if wordRemovalWeight u [p+j-t,j']=0 then 0 else
        natFourComputableUnitForm t left right s u
  | _,_ => 0

theorem natFourPrefixUnitForm_eq (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) :
    natFourPrefixUnitForm t left right s u=natFourComputableUnitForm t left right s u := by
  cases left with
  | none => cases right <;> rfl
  | some left =>
    rcases left with ⟨p,j⟩
    cases right with
    | none => rfl
    | some right =>
      rcases right with ⟨p',j'⟩
      change (if wordRemovalWeight u [p+j-t,j']=0 then 0 else
        natFourComputableUnitForm t (some (p,j)) (some (p',j')) s u)=_
      split
      · rename_i h
        exact (natFourComputableUnitForm_prefix_zero t p j p' j' s u h).symm
      · rfl

def natFourPrefixSourcePairContribution (t : ℕ) (s u : List ℕ)
    (pair : NatFourSourceColumnPair) : ℚ :=
  let F := natFourPrefixUnitForm t pair.1.1 pair.2.1 s u
  if F=0 then 0 else (natFourOriginalColumnGram t pair.1.2 pair.2.2 : ℚ)*F

def natFourPrefixGramForm (pairs : ℕ → List NatFourSourceColumnPair)
    (s u : List ℕ) : ℚ :=
  ((List.range 4).map fun t =>
    ((pairs t).map (natFourPrefixSourcePairContribution t s u)).sum).sum

theorem natFourPrefixGramForm_eq (pairs : ℕ → List NatFourSourceColumnPair)
    (s u : List ℕ) :
    natFourPrefixGramForm pairs s u=natFourActiveGramForm pairs s u := by
  unfold natFourPrefixGramForm natFourActiveGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair hp
  simp only [natFourPrefixSourcePairContribution,natFourSourcePairContribution,
    natFourPrefixUnitForm_eq]

theorem canonicalNatFourOriginalOperator_prefix_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (hsum : ∀ a, (basis a).sum=d)
    (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ a b, natFourPrefixGramForm pairs (basis a) (basis b)=M a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y)) =
      star x ⬝ᵥ (complexify M *ᵥ y) := by
  apply canonicalNatFourOriginalOperator_active_matrix_form d basis hlen hsum pairs hpairs M _ x y
  intro a b
  rw [← natFourPrefixGramForm_eq]
  exact hM a b

#print axioms natFour_removal_append
#print axioms natFour_removal_prefix_zero
#print axioms natFourComputableUnitForm_prefix_zero
#print axioms natFourPrefixUnitForm_eq
#print axioms natFourPrefixGramForm_eq
#print axioms canonicalNatFourOriginalOperator_prefix_matrix_form
end TorusLean.BosonFiniteCertificate
