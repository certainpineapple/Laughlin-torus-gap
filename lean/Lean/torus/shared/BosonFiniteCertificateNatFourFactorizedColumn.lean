import torus.shared.BosonFiniteCertificateNatFourFactorizedNormal
import torus.shared.BosonFiniteCertificateNatFourColumnCache

/-! Factorization of the original complete four-word column form into two
integer removal sums. The common original denominator is applied only after
summing the signed, independently checked original source-column Gram. -/
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

private theorem natFourFactor_list_flatMap_sum {ι A : Type*} [AddCommMonoid A]
    (l : List ι) (F : ι → List A) :
    (l.flatMap F).sum=(l.map fun a => (F a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons,List.map_cons,List.sum_cons,List.sum_append,ih]

private theorem natFourFactor_sum_product (l m : List ℕ) (F G : ℕ → ℚ) (c : ℚ) :
    ((l.flatMap fun a => m.map fun b => c*F a*G b)).sum=
      c*(l.map F).sum*(m.map G).sum := by
  rw [natFourFactor_list_flatMap_sum]
  simp only [List.sum_map_mul_left]
  rw [List.sum_map_mul_right,List.sum_map_mul_left]

def natFourColumnOutputRemoval (p j k : ℕ) (s : List ℕ) : ℕ :=
  ((List.range (p+1)).map fun a => wordRemovalWeight s [a,p-a,j,k]).sum

def natFourColumnInputRemoval (p k j : ℕ) (s : List ℕ) : ℕ :=
  ((List.range (p+1)).map fun b => wordRemovalWeight s [k,j,b,p-b]).sum

theorem natFourUnitColumnForm_factorized (t p j p' j' : ℕ) (s u : List ℕ)
    (hs : s.length=4) (hu : u.length=4) :
    natFourUnitColumnForm t (some (p,j)) (some (p',j')) s u=
      (((p+j-t).factorial*(p'+j'-t).factorial*
        natFourColumnOutputRemoval p j (p'+j'-t) s*
        natFourColumnInputRemoval p' (p+j-t) j' u : ℕ) : ℚ)/1000000000000000000000000 := by
  unfold natFourUnitColumnForm natFourColumnPairTerms natFourTermsForm
  simp only [List.map_flatMap,List.map_map,Function.comp_def,natFourOriginalTerm]
  simp_rw [natFour_original_term_complete_factor t p j p' j' _ _ s u hs hu]
  simp only [div_eq_mul_inv]
  have hrearr (a b : ℕ) :
      ((p+j-t).factorial : ℚ)*((p'+j'-t).factorial : ℚ)*
        (wordRemovalWeight s [a,p-a,j,p'+j'-t] : ℚ)*
        (wordRemovalWeight u [p+j-t,j',b,p'-b] : ℚ)*(1000000000000000000000000 : ℚ)⁻¹=
      (((p+j-t).factorial : ℚ)*((p'+j'-t).factorial : ℚ)*(1000000000000000000000000 : ℚ)⁻¹)*
        (wordRemovalWeight s [a,p-a,j,p'+j'-t] : ℚ)*
        (wordRemovalWeight u [p+j-t,j',b,p'-b] : ℚ) := by ring
  simp_rw [hrearr]
  rw [natFourFactor_sum_product]
  simp only [natFourColumnOutputRemoval,natFourColumnInputRemoval,Nat.cast_mul,
    Nat.cast_list_sum,List.map_map,Function.comp_def]
  ring

def natFourColumnNumerator (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) : ℕ :=
  match left,right with
  | some (p,j),some (p',j') =>
      if wordRemovalWeight s [j,p'+j'-t]=0 then 0 else
      if wordRemovalWeight u [p+j-t,j']=0 then 0 else
      (p+j-t).factorial*(p'+j'-t).factorial*
        natFourColumnOutputRemoval p j (p'+j'-t) s*
        natFourColumnInputRemoval p' (p+j-t) j' u
  | _,_ => 0

theorem natFourColumnNumerator_eq (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) (hs : s.length=4) (hu : u.length=4) :
    (natFourColumnNumerator t left right s u : ℚ)/1000000000000000000000000=
      natFourDualPrefixUnitForm t left right s u := by
  cases left with
  | none => cases right <;> simp [natFourColumnNumerator,natFourDualPrefixUnitForm]
  | some left =>
    rcases left with ⟨p,j⟩
    cases right with
    | none => simp [natFourColumnNumerator,natFourDualPrefixUnitForm]
    | some right =>
      rcases right with ⟨p',j'⟩
      by_cases hl : wordRemovalWeight s [j,p'+j'-t]=0
      · simp [natFourColumnNumerator,natFourDualPrefixUnitForm,hl]
      · by_cases hr : wordRemovalWeight u [p+j-t,j']=0
        · simp [natFourColumnNumerator,natFourDualPrefixUnitForm,natFourPrefixUnitForm,hl,hr]
        · simp only [natFourColumnNumerator,natFourDualPrefixUnitForm,natFourPrefixUnitForm,
            hl,hr,ite_false]
          rw [natFourComputableUnitForm_eq,natFourDegreeUnitColumnForm_eq _ _ _ s u hu,
            natFourUnitColumnForm_factorized t p j p' j' s u hs hu]

def natFourFactorizedCachedInteger (cache : ℕ → List NatFourColumnCacheEntry)
    (s u : List ℕ) : ℤ :=
  ((List.range 4).map fun t => ((cache t).map fun entry => entry.2*
    (natFourColumnNumerator t entry.1.1.1 entry.1.2.1 s u : ℤ)).sum).sum

def natFourFactorizedCachedGramForm (cache : ℕ → List NatFourColumnCacheEntry)
    (s u : List ℕ) : ℚ :=
  (natFourFactorizedCachedInteger cache s u : ℚ)/1000000000000000000000000

private theorem natFourFactor_int_sum (l : List ℤ) :
    (l.sum : ℚ)=(l.map fun z : ℤ => (z : ℚ)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.sum_cons,List.map_cons,Int.cast_add,ih]

private theorem natFourFactor_div_sum (l : List ℚ) (c : ℚ) :
    l.sum/c=(l.map fun a => a/c).sum := by
  simp only [div_eq_mul_inv,List.sum_map_mul_right,List.map_id_fun',id_eq]

theorem natFourFactorizedCachedGramForm_eq (cache : ℕ → List NatFourColumnCacheEntry)
    (s u : List ℕ) (hs : s.length=4) (hu : u.length=4) :
    natFourFactorizedCachedGramForm cache s u=natFourCachedGramForm cache s u := by
  unfold natFourFactorizedCachedGramForm natFourFactorizedCachedInteger natFourCachedGramForm
  rw [natFourFactor_int_sum,natFourFactor_div_sum]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [natFourFactor_int_sum,natFourFactor_div_sum]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro entry he
  rw [Int.cast_mul,Int.cast_natCast,mul_div_assoc,natFourColumnNumerator_eq t _ _ s u hs hu]
  unfold natFourCachedPairContribution
  dsimp only
  split <;> simp_all

theorem canonicalNatFourOriginalOperator_factorized_matrix_form {n : ℕ} (d : ℕ)
    (basis : Fin n → List ℕ) (hlen : ∀ a, (basis a).length=4)
    (hsum : ∀ a, (basis a).sum=d)
    (pairs : ℕ → List NatFourSourceColumnPair)
    (hpairs : ∀ t : Fin 4, pairs t.val=natFourActiveSourcePairs t.val d)
    (cache : ℕ → List NatFourColumnCacheEntry)
    (hc : ∀ t : Fin 4, cache t.val=natFourOriginalColumnCache t.val (pairs t.val))
    (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ a b, natFourFactorizedCachedGramForm cache (basis a) (basis b)=M a b)
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock basis x)
      (canonicalNatFourOriginalOperator (natFourWordBlock basis y))=
      star x ⬝ᵥ (complexify M *ᵥ y) := by
  apply canonicalNatFourOriginalOperator_cached_matrix_form d basis hlen hsum pairs hpairs cache hc M _ x y
  intro a b
  rw [← natFourFactorizedCachedGramForm_eq cache _ _ (hlen a) (hlen b)]
  exact hM a b

#print axioms natFourUnitColumnForm_factorized
#print axioms natFourColumnNumerator_eq
#print axioms natFourFactorizedCachedGramForm_eq
#print axioms canonicalNatFourOriginalOperator_factorized_matrix_form
end TorusLean.BosonFiniteCertificate
