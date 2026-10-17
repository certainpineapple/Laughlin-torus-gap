import torus.shared.BosonFiniteCertificateNatFourSparse
import torus.shared.BosonFiniteCertificateNatFourSupport

/-! Early total-degree sparsity for actual four-particle source forms.
The filter is proved from successful complete annihilation, independently of
all numerical target matrices. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

theorem natFour_removal_degree_zero (u labels : List ℕ)
    (hu : u.length=4) (hl : labels.length=4) (hd : labels.sum ≠ u.sum) :
    wordRemovalWeight u labels = 0 := by
  by_contra h
  have hlen := eraseWord_length_add u labels h
  have hsum := eraseWord_sum_add u labels h
  have hnil : eraseWord u labels = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [hnil,List.sum_nil,zero_add] at hsum
  exact hd hsum

theorem natFourUnitColumnForm_zero_degree (t p j p' j' : ℕ) (s u : List ℕ)
    (hu : u.length=4) (hd : (p+j-t)+j'+p' ≠ u.sum) :
    natFourUnitColumnForm t (some (p,j)) (some (p',j')) s u = 0 := by
  unfold natFourUnitColumnForm natFourColumnPairTerms
  rw [natFourTermsForm_flatMap]
  apply List.sum_eq_zero
  intro z hz
  rcases List.mem_map.mp hz with ⟨a,ha,rfl⟩
  unfold natFourTermsForm
  rw [List.map_map]
  apply List.sum_eq_zero
  intro z hz
  rcases List.mem_map.mp hz with ⟨b,hb,rfl⟩
  have hbp : b ≤ p' := Nat.le_of_lt_succ (List.mem_range.mp hb)
  have hsum : [p+j-t,j',b,p'-b].sum ≠ u.sum := by
    change (p+j-t)+(j'+(b+((p'-b)+0))) ≠ u.sum
    omega
  have hw := natFour_removal_degree_zero u [p+j-t,j',b,p'-b] hu rfl hsum
  simp only [Function.comp_def,natFourOriginalTerm,natFourNormalWordForm,hw,Nat.cast_zero,zero_mul]
  split_ifs <;> simp

def natFourDegreeUnitColumnForm (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) : ℚ :=
  match left,right with
  | some (p,j),some (p',j') =>
      if (p+j-t)+j'+p' = u.sum then
        natFourUnitColumnFormSparse t left right s u else 0
  | _,_ => 0

theorem natFourDegreeUnitColumnForm_eq (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) (hu : u.length=4) :
    natFourDegreeUnitColumnForm t left right s u = natFourUnitColumnForm t left right s u := by
  cases left with
  | none => simp [natFourDegreeUnitColumnForm,natFourUnitColumnForm,natFourColumnPairTerms,natFourTermsForm]
  | some left =>
    rcases left with ⟨p,j⟩
    cases right with
    | none => simp [natFourDegreeUnitColumnForm,natFourUnitColumnForm,natFourColumnPairTerms,natFourTermsForm]
    | some right =>
      rcases right with ⟨p',j'⟩
      by_cases h : (p+j-t)+j'+p'=u.sum
      · simp only [natFourDegreeUnitColumnForm,h,ite_true,natFourUnitColumnFormSparse_eq]
      · simp only [natFourDegreeUnitColumnForm,h,ite_false,
          natFourUnitColumnForm_zero_degree t p j p' j' s u hu h]

def natFourDegreeChannelGramForm (t : ℕ) (s u : List ℕ) : ℚ :=
  ((natFourColumnSlots t).map fun i => ((natFourColumnSlots t).map fun j =>
    let F := natFourDegreeUnitColumnForm t
      (natFourSourceColumn t i) (natFourSourceColumn t j) s u
    if F=0 then 0 else (natFourOriginalColumnGram t i j : ℚ)*F).sum).sum

theorem natFourDegreeChannelGramForm_eq (t : ℕ) (s u : List ℕ) (hu : u.length=4) :
    natFourDegreeChannelGramForm t s u = natFourChannelGramForm t s u := by
  unfold natFourDegreeChannelGramForm natFourChannelGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  dsimp only
  rw [natFourDegreeUnitColumnForm_eq t _ _ s u hu]
  by_cases h : natFourUnitColumnForm t (natFourSourceColumn t i) (natFourSourceColumn t j) s u=0
  · simp [h]
  · simp [h]

def natFourDegreeOriginalGramForm (s u : List ℕ) : ℚ :=
  ((List.range 4).map fun t => natFourDegreeChannelGramForm t s u).sum

theorem natFourDegreeOriginalGramForm_eq (s u : List ℕ) (hu : u.length=4) :
    natFourDegreeOriginalGramForm s u = natFourOriginalGramForm s u := by
  unfold natFourDegreeOriginalGramForm natFourOriginalGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact natFourDegreeChannelGramForm_eq t s u hu

theorem canonicalNatFourOriginalOperator_degree_form (s u : List ℕ) (hu : u.length=4) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourOriginalOperator (scaledWord factorialRootNat u)) =
      (natFourDegreeOriginalGramForm s u : ℂ) := by
  rw [natFourDegreeOriginalGramForm_eq s u hu,canonicalNatFourOriginalOperator_gram_form]

#print axioms natFour_removal_degree_zero
#print axioms natFourUnitColumnForm_zero_degree
#print axioms natFourDegreeUnitColumnForm_eq
#print axioms natFourDegreeChannelGramForm_eq
#print axioms natFourDegreeOriginalGramForm_eq
#print axioms canonicalNatFourOriginalOperator_degree_form
end TorusLean.BosonFiniteCertificate
