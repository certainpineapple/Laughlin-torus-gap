import torus.shared.BosonFiniteCertificateNatFourFactorizedColumn
import torus.shared.BosonFiniteCertificateNatPairNormalizedRank

/-! Exact Euler count for the two particles left after a spectator prefix.
On a true four-word of the matching degree, the complete ordered pair sum
is twice the prefix removal, even when the two remaining labels coincide.
This eliminates numeric pair loops while preserving the genuine factorial
word action and every original signed coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

theorem natFour_removal_labels_perm_complete (s labels other : List ℕ)
    (hlen : s.length=labels.length) (hp : labels.Perm other) :
    wordRemovalWeight s labels=wordRemovalWeight s other := by
  by_cases hs : s.Perm labels
  · have ho := hs.trans hp
    rw [natFour_removal_input_perm s labels labels hs,natFour_removal_self,
      natFour_removal_input_perm s other other ho,natFour_removal_self,
      natFourMultiplicity_eq_weight,natFourMultiplicity_eq_weight,
      (natFourOccupation_eq_iff_perm labels other).mpr hp]
  · have ho : ¬s.Perm other := fun h => hs (h.trans hp.symm)
    rw [natFour_removal_zero_of_not_perm s labels hlen hs,
      natFour_removal_zero_of_not_perm s other (hlen.trans hp.length_eq) ho]

/-- Every ordered two-particle removal is counted. Distinct labels give
one contribution each; an equal pair gives the genuine falling factorial 2. -/
theorem natFour_pair_removal_sum (p : ℕ) (s : List ℕ)
    (hlen : s.length=2) (hsum : s.sum=p) :
    ((List.range (p+1)).map fun a => wordRemovalWeight s [a,p-a]).sum=2 := by
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
  have hp : p=a+b := by simpa only [List.sum_cons,List.sum_nil,Nat.add_zero] using hsum.symm
  rw [hp]
  have hw (k : ℕ) : wordRemovalWeight [a,b] [k,a+b-k]=
      (if k=a then 1 else 0)+(if k=b then 1 else 0) := by
    by_cases hka : k=a
    · subst k
      by_cases hab : a=b
      · subst b
        simp [wordRemovalWeight]
      · simp [wordRemovalWeight,hab]
    · by_cases hkb : k=b
      · subst k
        simp [wordRemovalWeight,hka,Ne.symm hka]
      · have hc : ([a,b] : List ℕ).count k=0 := by
          apply List.count_eq_zero.mpr
          simp [hka,hkb]
        simp only [wordRemovalWeight,hc,Nat.zero_mul,if_neg hka,if_neg hkb,Nat.zero_add]
  rw [nat_pair_list_range_sum (a+b+1)
    (fun k => wordRemovalWeight [a,b] [k,a+b-k])]
  simp_rw [hw]
  rw [Finset.sum_add_distrib]
  have ha : a ∈ Finset.range (a+b+1) := Finset.mem_range.mpr (by omega)
  have hb : b ∈ Finset.range (a+b+1) := Finset.mem_range.mpr (by omega)
  simp [ha,hb]

theorem natFour_complete_pair_prefix_sum (p : ℕ) (s first : List ℕ)
    (hs : s.length=4) (hf : first.length=2) (hd : s.sum=first.sum+p) :
    ((List.range (p+1)).map fun a => wordRemovalWeight s (first++[a,p-a])).sum=
      2*wordRemovalWeight s first := by
  simp_rw [natFour_removal_append]
  rw [List.sum_map_mul_left]
  by_cases hz : wordRemovalWeight s first=0
  · rw [hz,Nat.zero_mul,Nat.mul_zero]
  · have hlen : (eraseWord s first).length=2 := by
      have h := eraseWord_length_add s first hz
      omega
    have hsum : (eraseWord s first).sum=p := by
      have h := eraseWord_sum_add s first hz
      omega
    rw [natFour_pair_removal_sum p _ hlen hsum,Nat.mul_comm]

theorem natFourColumnOutputRemoval_prefix (p j k : ℕ) (s : List ℕ)
    (hs : s.length=4) (hd : s.sum=p+j+k) :
    natFourColumnOutputRemoval p j k s=2*wordRemovalWeight s [j,k] := by
  have hperm (a : ℕ) : wordRemovalWeight s [a,p-a,j,k]=
      wordRemovalWeight s ([j,k]++[a,p-a]) :=
    natFour_removal_labels_perm_complete s [a,p-a,j,k] ([j,k]++[a,p-a]) hs
      (List.perm_append_comm (l₁ := [a,p-a]) (l₂ := [j,k]))
  simp_rw [natFourColumnOutputRemoval,hperm]
  exact natFour_complete_pair_prefix_sum p s [j,k] hs rfl
    (by simp only [List.sum_cons,List.sum_nil,Nat.add_zero]; omega)

theorem natFourColumnInputRemoval_prefix (p k j : ℕ) (s : List ℕ)
    (hs : s.length=4) (hd : s.sum=k+j+p) :
    natFourColumnInputRemoval p k j s=2*wordRemovalWeight s [k,j] := by
  exact natFour_complete_pair_prefix_sum p s [k,j] hs rfl
    (by simpa only [List.sum_cons,List.sum_nil,Nat.add_zero] using hd)

def natFourPrefixColumnNumerator (t : ℕ) (left right : Option (ℕ × ℕ))
    (s u : List ℕ) : ℕ :=
  match left,right with
  | some (p,j),some (p',j') =>
      4*(p+j-t).factorial*(p'+j'-t).factorial*
        wordRemovalWeight s [j,p'+j'-t]*wordRemovalWeight u [p+j-t,j']
  | _,_ => 0

theorem natFourColumnNumerator_prefix (t p j p' j' : ℕ) (s u : List ℕ)
    (hs : s.length=4) (hu : u.length=4)
    (hds : s.sum=p+j+(p'+j'-t)) (hdu : u.sum=(p+j-t)+j'+p') :
    natFourColumnNumerator t (some (p,j)) (some (p',j')) s u=
      natFourPrefixColumnNumerator t (some (p,j)) (some (p',j')) s u := by
  dsimp only [natFourColumnNumerator,natFourPrefixColumnNumerator]
  by_cases hz : wordRemovalWeight s [j,p'+j'-t]=0
  · simp [hz]
  · by_cases hz' : wordRemovalWeight u [p+j-t,j']=0
    · simp [hz']
    · rw [if_neg hz,if_neg hz',natFourColumnOutputRemoval_prefix p j (p'+j'-t) s hs hds,
        natFourColumnInputRemoval_prefix p' (p+j-t) j' u hu hdu]
      ring

#print axioms natFour_removal_labels_perm_complete
#print axioms natFour_pair_removal_sum
#print axioms natFour_complete_pair_prefix_sum
#print axioms natFourColumnOutputRemoval_prefix
#print axioms natFourColumnInputRemoval_prefix
#print axioms natFourColumnNumerator_prefix
end TorusLean.BosonFiniteCertificate
