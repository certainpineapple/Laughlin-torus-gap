import torus.shared.BosonFiniteCertificateNatFourDualPrefixSparse

/-! Checked source-column Gram caches. The cached integers are compared with
original row sums before use; no target M4 matrix supplies cache coefficients.
This avoids recomputing a large original row dot product in every word entry. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

abbrev NatFourColumnCacheEntry := NatFourSourceColumnPair × ℤ

def natFourOriginalColumnCache (t : ℕ) (pairs : List NatFourSourceColumnPair) :
    List NatFourColumnCacheEntry :=
  pairs.map fun pair => (pair,natFourOriginalColumnGram t pair.1.2 pair.2.2)

def natFourCachedPairContribution (t : ℕ) (s u : List ℕ) (entry : NatFourColumnCacheEntry) : ℚ :=
  let F := natFourDualPrefixUnitForm t entry.1.1.1 entry.1.2.1 s u
  if F=0 then 0 else (entry.2 : ℚ)*F

def natFourCachedGramForm (cache : ℕ → List NatFourColumnCacheEntry) (s u : List ℕ) : ℚ :=
  ((List.range 4).map fun t => ((cache t).map (natFourCachedPairContribution t s u)).sum).sum

theorem natFourCachedGramForm_eq (pairs : ℕ → List NatFourSourceColumnPair)
    (cache : ℕ → List NatFourColumnCacheEntry)
    (hc : ∀ t : Fin 4, cache t.val=natFourOriginalColumnCache t.val (pairs t.val))
    (s u : List ℕ) :
    natFourCachedGramForm cache s u=natFourDualPrefixGramForm pairs s u := by
  unfold natFourCachedGramForm natFourDualPrefixGramForm
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [hc ⟨t,List.mem_range.mp ht⟩]
  simp only [natFourOriginalColumnCache,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair hp
  rfl

theorem canonicalNatFourOriginalOperator_cached_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (hsum : ∀ a, (basis a).sum=d)
    (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (cache : ℕ → List NatFourColumnCacheEntry)
    (hc : ∀ t : Fin 4, cache t.val=natFourOriginalColumnCache t.val (pairs t.val))
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ a b, natFourCachedGramForm cache (basis a) (basis b)=M a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y)) =
      star x ⬝ᵥ (complexify M *ᵥ y) := by
  apply canonicalNatFourOriginalOperator_dual_prefix_matrix_form d basis hlen hsum pairs hpairs M _ x y
  intro a b
  rw [← natFourCachedGramForm_eq pairs cache hc]
  exact hM a b

#print axioms natFourCachedGramForm_eq
#print axioms canonicalNatFourOriginalOperator_cached_matrix_form
end TorusLean.BosonFiniteCertificate
