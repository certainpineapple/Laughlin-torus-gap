import torus.shared.BosonFiniteCertificateNatFourIndexedColumns

/-! Exact source-column degree selection before numeric evaluation. Every
omitted pair has zero true complete-annihilation form; the active lists are
checked against the original column product, never against a target matrix. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateConjugation

abbrev NatFourSourceColumnPair :=
  (Option (ℕ × ℕ) × ℕ) × (Option (ℕ × ℕ) × ℕ)

def natFourSourceColumnPairs (t : ℕ) : List NatFourSourceColumnPair :=
  (natFourDecodedColumns t).flatMap fun left =>
    (natFourDecodedColumns t).map fun right => (left,right)

def natFourSourcePairDegree (t : ℕ) (pair : NatFourSourceColumnPair) : Option ℕ :=
  match pair.1.1,pair.2.1 with
  | some (p,j),some (p',j') => some ((p+j-t)+j'+p')
  | _,_ => none

def natFourSourcePairContribution (t : ℕ) (s u : List ℕ) (pair : NatFourSourceColumnPair) : ℚ :=
  let F := natFourComputableUnitForm t pair.1.1 pair.2.1 s u
  if F=0 then 0 else (natFourOriginalColumnGram t pair.1.2 pair.2.2 : ℚ)*F

private theorem natFourActive_list_flatMap_sum {ι A : Type*} [AddCommMonoid A]
    (l : List ι) (F : ι → List A) :
    (l.flatMap F).sum=(l.map fun a => (F a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

theorem natFourSourceColumnPairs_form (t : ℕ) (s u : List ℕ) :
    ((natFourSourceColumnPairs t).map (natFourSourcePairContribution t s u)).sum=
      natFourIndexedChannelForm t s u := by
  simp only [natFourSourceColumnPairs,List.map_flatMap,natFourActive_list_flatMap_sum,
    List.map_map,Function.comp_def,natFourSourcePairContribution,natFourIndexedChannelForm]

theorem natFourSourcePairContribution_wrong_degree (t : ℕ) (s u : List ℕ)
    (pair : NatFourSourceColumnPair) (hd : natFourSourcePairDegree t pair ≠ some u.sum) :
    natFourSourcePairContribution t s u pair=0 := by
  rcases pair with ⟨⟨left,i⟩,⟨right,k⟩⟩
  cases left with
  | none => simp [natFourSourcePairContribution,natFourComputableUnitForm]
  | some left =>
    rcases left with ⟨p,j⟩
    cases right with
    | none => simp [natFourSourcePairContribution,natFourComputableUnitForm]
    | some right =>
      rcases right with ⟨p',j'⟩
      have hh : (p+j-t)+j'+p' ≠ u.sum := by
        simpa only [natFourSourcePairDegree,ne_eq,Option.some.injEq] using hd
      simp [natFourSourcePairContribution,natFourComputableUnitForm,hh]

def natFourActiveSourcePairs (t d : ℕ) : List NatFourSourceColumnPair :=
  (natFourSourceColumnPairs t).filter fun pair => decide (natFourSourcePairDegree t pair=some d)

private theorem natFourActive_filter_sum {ι : Type*} (l : List ι) (p : ι → Bool) (F : ι → ℚ)
    (hz : ∀ a, p a=false → F a=0) :
    ((l.filter p).map F).sum=(l.map F).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a
    · simp [hp,hz a hp,ih]
    · simp [hp,ih]

theorem natFourActiveSourcePairs_form (t d : ℕ) (s u : List ℕ) (hu : u.sum=d) :
    ((natFourActiveSourcePairs t d).map (natFourSourcePairContribution t s u)).sum=
      natFourIndexedChannelForm t s u := by
  rw [natFourActiveSourcePairs,natFourActive_filter_sum]
  · exact natFourSourceColumnPairs_form t s u
  · intro pair hp
    apply natFourSourcePairContribution_wrong_degree t s u pair
    rw [hu]
    exact of_decide_eq_false hp

def natFourActiveGramForm (pairs : ℕ → List NatFourSourceColumnPair) (s u : List ℕ) : ℚ :=
  ((List.range 4).map fun t => ((pairs t).map (natFourSourcePairContribution t s u)).sum).sum

theorem natFourActiveGramForm_eq (d : ℕ) (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (s u : List ℕ) (hu : u.sum=d) :
    natFourActiveGramForm pairs s u=natFourIndexedGramForm s u := by
  unfold natFourActiveGramForm natFourIndexedGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [hpairs ⟨t,List.mem_range.mp ht⟩]
  exact natFourActiveSourcePairs_form t d s u hu

theorem canonicalNatFourOriginalOperator_active_form (d : ℕ)
    (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (s u : List ℕ) (hlen : u.length=4) (hu : u.sum=d) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourOriginalOperator (scaledWord factorialRootNat u)) =
      (natFourActiveGramForm pairs s u : ℂ) := by
  rw [natFourActiveGramForm_eq d pairs hpairs s u hu,
    canonicalNatFourOriginalOperator_indexed_form s u hlen]

#print axioms natFourSourceColumnPairs_form
#print axioms natFourSourcePairContribution_wrong_degree
#print axioms natFourActiveSourcePairs_form
#print axioms natFourActiveGramForm_eq
#print axioms canonicalNatFourOriginalOperator_active_form
end TorusLean.BosonFiniteCertificate
