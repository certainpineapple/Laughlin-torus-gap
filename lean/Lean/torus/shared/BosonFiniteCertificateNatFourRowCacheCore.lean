import torus.shared.BosonFiniteCertificateNatFourFactorizedColumn

/-! A source-only row filter. It discards precisely columns whose two fixed
creation labels cannot occur in the actual left occupation word. Checked row
caches may use this identity to avoid traversing the full source list again
for every right word. No numerical target matrix participates in the filter. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateWords
open Matrix
open scoped BigOperators

def natFourSourceRowKeep (t : ℕ) (s : List ℕ)
    (entry : NatFourColumnCacheEntry) : Bool :=
  match entry.1.1.1,entry.1.2.1 with
  | some (_,j),some (p',j') => decide (wordRemovalWeight s [j,p'+j'-t]≠0)
  | _,_ => false

def natFourSourceRowCache (cache : ℕ → List NatFourColumnCacheEntry)
    (s : List ℕ) (t : ℕ) : List NatFourColumnCacheEntry :=
  (cache t).filter (natFourSourceRowKeep t s)

theorem natFourColumnNumerator_zero_of_row_discard (t : ℕ) (s u : List ℕ)
    (entry : NatFourColumnCacheEntry) (h : natFourSourceRowKeep t s entry=false) :
    natFourColumnNumerator t entry.1.1.1 entry.1.2.1 s u=0 := by
  rcases entry with ⟨⟨⟨left,i⟩,⟨right,j⟩⟩,c⟩
  cases left with
  | none => simp [natFourColumnNumerator]
  | some left =>
    rcases left with ⟨p,k⟩
    cases right with
    | none => simp [natFourColumnNumerator]
    | some right =>
      rcases right with ⟨q,l⟩
      by_cases hz : wordRemovalWeight s [k,q+l-t]=0
      · simp [natFourColumnNumerator,hz]
      · simp [natFourSourceRowKeep,hz] at h

theorem natFourSourceRowCache_integer_sum (t : ℕ) (s u : List ℕ)
    (entries : List NatFourColumnCacheEntry) :
    (((entries.filter (natFourSourceRowKeep t s)).map fun entry => entry.2*
      (natFourColumnNumerator t entry.1.1.1 entry.1.2.1 s u : ℤ)).sum)=
    ((entries.map fun entry => entry.2*
      (natFourColumnNumerator t entry.1.1.1 entry.1.2.1 s u : ℤ)).sum) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    by_cases h : natFourSourceRowKeep t s entry=true
    · simp only [List.filter_cons_of_pos h,List.map_cons,List.sum_cons,ih]
    · have hf : natFourSourceRowKeep t s entry=false := Bool.eq_false_of_ne_true h
      have hz := natFourColumnNumerator_zero_of_row_discard t s u entry hf
      simp only [List.filter_cons_of_neg h,List.map_cons,
        List.sum_cons,hz,Nat.cast_zero,mul_zero,zero_add,ih]

theorem natFourFactorizedCachedGramForm_row_filter
    (cache : ℕ → List NatFourColumnCacheEntry) (s u : List ℕ) :
    natFourFactorizedCachedGramForm (natFourSourceRowCache cache s) s u=
      natFourFactorizedCachedGramForm cache s u := by
  unfold natFourFactorizedCachedGramForm natFourFactorizedCachedInteger
  apply congrArg (fun z : ℤ => (z : ℚ)/1000000000000000000000000)
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact natFourSourceRowCache_integer_sum t s u (cache t)

theorem canonicalNatFourOriginalOperator_row_cached_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (hsum : ∀ a, (basis a).sum=d)
    (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (cache : ℕ → List NatFourColumnCacheEntry)
    (hc : ∀ t : Fin 4, cache t.val=natFourOriginalColumnCache t.val (pairs t.val))
    (rowCache : Fin n → ℕ → List NatFourColumnCacheEntry)
    (hr : ∀ a t, rowCache a t=natFourSourceRowCache cache (basis a) t)
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ a b, natFourFactorizedCachedGramForm (rowCache a) (basis a) (basis b)=M a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y))=
      star x ⬝ᵥ (complexify M *ᵥ y) := by
  apply canonicalNatFourOriginalOperator_factorized_matrix_form d basis hlen hsum
    pairs hpairs cache hc M _ x y
  intro a b
  have he : rowCache a=natFourSourceRowCache cache (basis a) := funext (hr a)
  rw [← natFourFactorizedCachedGramForm_row_filter cache (basis a) (basis b),←he]
  exact hM a b

#print axioms natFourColumnNumerator_zero_of_row_discard
#print axioms natFourSourceRowCache_integer_sum
#print axioms natFourFactorizedCachedGramForm_row_filter
#print axioms canonicalNatFourOriginalOperator_row_cached_matrix_form
end TorusLean.BosonFiniteCertificate
