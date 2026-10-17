import torus.shared.BosonFiniteCertificateNatFourPrefixCollapse
import torus.shared.BosonFiniteCertificateNatFourRowCacheCore

/-! Fast signed integer source evaluation after the proved complete-pair
Euler count. Compatible degrees are separately checked on source caches;
none of the filters, degree conditions, or weights depend on a target M4
entry. The old true operator transport is reused without changing its source. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

def natFourCacheDegreeCompatible (d t : ℕ) (entry : NatFourColumnCacheEntry) : Bool :=
  match entry.1.1.1,entry.1.2.1 with
  | some (p,j),some (p',j') => decide (p+j+(p'+j'-t)=d ∧ (p+j-t)+j'+p'=d)
  | _,_ => true

private theorem natFourDecodedColumns_lower_bound (t : Fin 4)
    (entry : Option (ℕ × ℕ) × ℕ) (he : entry ∈ natFourDecodedColumns t.val) :
    match entry.1 with
    | none => True
    | some (p,j) => t.val ≤ p+j := by
  have h : (natFourDecodedColumns t.val).all (fun c => match c.1 with
      | none => true
      | some (p,j) => decide (t.val ≤ p+j))=true := by
    fin_cases t <;> decide +kernel
  have hh := List.all_eq_true.mp h entry he
  rcases entry with ⟨e,k⟩
  cases e with
  | none => trivial
  | some e => exact of_decide_eq_true hh

/-- Matching output degree follows from the actual source-column bounds,
not from a separately tested target table. -/
theorem natFourSourceCache_degree (d : ℕ)
    (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (cache : ℕ → List NatFourColumnCacheEntry)
    (hc : ∀ t : Fin 4, cache t.val=natFourOriginalColumnCache t.val (pairs t.val)) :
    ∀ t : Fin 4, ∀ entry ∈ cache t.val, natFourCacheDegreeCompatible d t.val entry=true := by
  intro t entry he
  rw [hc t,natFourOriginalColumnCache,hpairs t] at he
  rcases List.mem_map.mp he with ⟨pair,hp,rfl⟩
  rcases List.mem_filter.mp hp with ⟨hcols,hdegree⟩
  rcases List.mem_flatMap.mp hcols with ⟨left,hl,hrest⟩
  rcases List.mem_map.mp hrest with ⟨right,hr,rfl⟩
  have hleft := natFourDecodedColumns_lower_bound t left hl
  have hright := natFourDecodedColumns_lower_bound t right hr
  rcases left with ⟨left,a⟩
  rcases right with ⟨right,b⟩
  cases left with
  | none => cases right <;> rfl
  | some left =>
    rcases left with ⟨p,j⟩
    cases right with
    | none => rfl
    | some right =>
      rcases right with ⟨p',j'⟩
      have hd : (p+j-t.val)+j'+p'=d := by
        exact Option.some.inj (of_decide_eq_true hdegree)
      change decide (p+j+(p'+j'-t.val)=d ∧ (p+j-t.val)+j'+p'=d)=true
      apply decide_eq_true
      change t.val ≤ p+j at hleft
      change t.val ≤ p'+j' at hright
      omega

def natFourPrefixCollapsedInteger (cache : ℕ → List NatFourColumnCacheEntry)
    (s u : List ℕ) : ℤ :=
  ((List.range 4).map fun t => ((cache t).map fun entry => entry.2*
    (natFourPrefixColumnNumerator t entry.1.1.1 entry.1.2.1 s u : ℤ)).sum).sum

def natFourPrefixCollapsedForm (cache : ℕ → List NatFourColumnCacheEntry)
    (s u : List ℕ) : ℚ :=
  (natFourPrefixCollapsedInteger cache s u : ℚ)/1000000000000000000000000

theorem natFourPrefixCollapsedForm_eq (d : ℕ) (cache : ℕ → List NatFourColumnCacheEntry)
    (hd : ∀ t : Fin 4, ∀ entry ∈ cache t.val, natFourCacheDegreeCompatible d t.val entry=true)
    (s u : List ℕ) (hs : s.length=4) (hu : u.length=4)
    (hds : s.sum=d) (hdu : u.sum=d) :
    natFourPrefixCollapsedForm cache s u=natFourFactorizedCachedGramForm cache s u := by
  unfold natFourPrefixCollapsedForm natFourFactorizedCachedGramForm
  apply congrArg (fun z : ℤ => (z : ℚ)/1000000000000000000000000)
  unfold natFourPrefixCollapsedInteger natFourFactorizedCachedInteger
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry he
  have hd' := hd ⟨t,List.mem_range.mp ht⟩ entry he
  rcases entry with ⟨⟨⟨left,a⟩,⟨right,b⟩⟩,c⟩
  cases left with
  | none => cases right <;> rfl
  | some left =>
    rcases left with ⟨p,j⟩
    cases right with
    | none => rfl
    | some right =>
      rcases right with ⟨p',j'⟩
      have hh : p+j+(p'+j'-t)=d ∧ (p+j-t)+j'+p'=d := of_decide_eq_true hd'
      rw [natFourColumnNumerator_prefix t p j p' j' s u hs hu
        (hds.trans hh.1.symm) (hdu.trans hh.2.symm)]

theorem natFourSourceRowCache_degree (d : ℕ) (cache : ℕ → List NatFourColumnCacheEntry)
    (hd : ∀ t : Fin 4, ∀ entry ∈ cache t.val, natFourCacheDegreeCompatible d t.val entry=true)
    (s : List ℕ) :
    ∀ t : Fin 4, ∀ entry ∈ natFourSourceRowCache cache s t.val,
      natFourCacheDegreeCompatible d t.val entry=true := by
  intro t entry he
  exact hd t entry (List.mem_filter.mp he).1

theorem canonicalNatFourOriginalOperator_prefix_collapsed_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (hsum : ∀ a, (basis a).sum=d)
    (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (cache : ℕ → List NatFourColumnCacheEntry)
    (hc : ∀ t : Fin 4, cache t.val=natFourOriginalColumnCache t.val (pairs t.val))
    (rowCache : Fin n → ℕ → List NatFourColumnCacheEntry)
    (hr : ∀ a t, rowCache a t=natFourSourceRowCache cache (basis a) t)
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ a b, natFourPrefixCollapsedForm (rowCache a) (basis a) (basis b)=M a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y))=
      star x ⬝ᵥ (complexify M *ᵥ y) := by
  apply canonicalNatFourOriginalOperator_row_cached_matrix_form d basis hlen hsum
    pairs hpairs cache hc rowCache hr M _ x y
  intro a b
  have hd : ∀ t : Fin 4, ∀ entry ∈ rowCache a t.val,
      natFourCacheDegreeCompatible d t.val entry=true := by
    intro t entry he
    rw [hr a t.val] at he
    exact natFourSourceRowCache_degree d cache
      (natFourSourceCache_degree d pairs hpairs cache hc) (basis a) t entry he
  rw [←natFourPrefixCollapsedForm_eq d (rowCache a) hd _ _
    (hlen a) (hlen b) (hsum a) (hsum b)]
  exact hM a b

#print axioms natFourSourceCache_degree
#print axioms natFourPrefixCollapsedForm_eq
#print axioms natFourSourceRowCache_degree
#print axioms canonicalNatFourOriginalOperator_prefix_collapsed_matrix_form
end TorusLean.BosonFiniteCertificate
