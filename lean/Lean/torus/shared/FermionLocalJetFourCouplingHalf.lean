import torus.shared.FermionLocalJetFourCouplingParity
import Mathlib.Data.Fin.Rev

/-! The exact factor two passing from ordered spectator modes to j<k.
The diagonal of every odd row vanishes, and exchange contributes two minus
signs to a row inner product. No physical jet orthogonality is used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators ComplexConjugate

theorem s45_rows_orthonormal (z w T : ℕ) :
    (∑ p : Fin (T+1), star (s45 z T p.val) * s45 w T p.val) =
      if z=w ∧ z≤T then 1 else 0 := by
  classical
  by_cases hz : z≤T
  · by_cases hw : w≤T
    · let z' : Fin (T+1) := ⟨z,Nat.lt_succ_of_le hz⟩
      let w' : Fin (T+1) := ⟨w,Nat.lt_succ_of_le hw⟩
      have h := coefficient45_rows_orthonormal T z' w'
      simp only [← s45_in_range] at h
      simpa [z',w',hz] using h
    · have hzero (p : Fin (T+1)) : s45 w T p.val=0 :=
        s45_outside w T p.val (Or.inl (Nat.lt_of_not_ge hw))
      have hn : ¬(z=w ∧ z≤T) := by rintro ⟨rfl,hz⟩; exact hw hz
      simp only [hzero,mul_zero,Finset.sum_const_zero,if_neg hn]
  · have hzero (p : Fin (T+1)) : s45 z T p.val=0 :=
      s45_outside z T p.val (Or.inl (Nat.lt_of_not_ge hz))
    simp only [hzero,star_zero,zero_mul,Finset.sum_const_zero,and_false,hz,if_false]

/-- Extending a complete coefficient row by its genuine zero coefficients
does not change its norm. This handles the varying outer degree D-r. -/
theorem s45_row_norm_extended (z T M : ℕ) (hz : z≤T) (hTM : T≤M) :
    (∑ p : Fin (M+1), star (s45 z T p.val) * s45 z T p.val) = 1 := by
  let f : ℕ → ℂ := fun p => star (s45 z T p) * s45 z T p
  have he : (∑ p ∈ Finset.range (M+1), f p) = ∑ p ∈ Finset.range (T+1), f p := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro p hp hnot
    have hout : T<p := by simp only [Finset.mem_range] at hnot; omega
    simp only [f,s45_outside z T p (Or.inr hout),star_zero,zero_mul]
  rw [Fin.sum_univ_eq_sum_range (fun p => star (s45 z T p) * s45 z T p) (M+1)]
  change (∑ p ∈ Finset.range (M+1), f p) = 1
  rw [he]
  change (∑ p ∈ Finset.range (T+1), star (s45 z T p) * s45 z T p) = 1
  rw [← Fin.sum_univ_eq_sum_range (fun p => star (s45 z T p) * s45 z T p) (T+1),
    s45_rows_orthonormal]
  simp [hz]

private theorem rev_val (n : ℕ) (j : Fin (n+1)) : j.rev.val=n-j.val := by
  change n+1-(j.val+1)=n-j.val
  omega

private theorem symmetric_half_sum (n : ℕ) (f : Fin (n+1) → ℂ)
    (hsym : ∀ j, f j.rev=f j) (hdiag : ∀ j, j=j.rev → f j=0) :
    2 * (∑ j : Fin (n+1), if j<j.rev then f j else 0) = ∑ j, f j := by
  classical
  have hs (j : Fin (n+1)) : f j =
      (if j<j.rev then f j else 0) + (if j.rev<j then f j else 0) := by
    rcases lt_trichotomy j j.rev with h | h | h
    · simp [h,not_lt.mpr h.le]
    · simp only [hdiag j h,ite_self,add_zero]
    · simp [h,not_lt.mpr h.le]
  have hr : (∑ j : Fin (n+1), if j.rev<j then f j else 0) =
      ∑ j : Fin (n+1), if j<j.rev then f j else 0 := by
    simpa only [Fin.revPerm_apply,Fin.rev_rev,hsym] using
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n+1)))
        (fun j => if j.rev<j then f j else 0)).symm
  calc
    _ = (∑ j : Fin (n+1), if j<j.rev then f j else 0) +
        ∑ j : Fin (n+1), if j.rev<j then f j else 0 := by rw [hr]; ring
    _ = ∑ j, f j := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _ => (hs j).symm)

/-- The original sqrt(2) in S exactly compensates the unordered spectator
half-space. Every odd copy is retained, including columns whose later wedge
image may vanish. -/
theorem s45_odd_half_rows (r s n : ℕ) (hr : Odd r) (hs : Odd s) :
    2 * (∑ j : Fin (n+1), if j.val<n-j.val then
      star (s45 r n j.val) * s45 s n j.val else 0) =
      if r=s ∧ r≤n then 1 else 0 := by
  classical
  by_cases hrn : r≤n
  · by_cases hsn : s≤n
    · let f : Fin (n+1) → ℂ := fun j => star (s45 r n j.val) * s45 s n j.val
      have hsym (j : Fin (n+1)) : f j.rev=f j := by
        dsimp only [f]
        rw [rev_val,s45_reflection r n j.val hrn (Nat.le_of_lt_succ j.isLt),
          s45_reflection s n j.val hsn (Nat.le_of_lt_succ j.isLt),hr.neg_one_pow,hs.neg_one_pow]
        simp
      have hdiag (j : Fin (n+1)) (hj : j=j.rev) : f j=0 := by
        have hv := congrArg Fin.val hj
        rw [rev_val] at hv
        have hn : n=2*j.val := by have := j.isLt; omega
        have hz : s45 r n j.val=0 := by
          have hz := s45_diagonal_odd_zero r j.val (by omega) hr
          simpa only [← hn] using hz
        simp only [f,hz,star_zero,zero_mul]
      have h := symmetric_half_sum n f hsym hdiag
      simp only [Fin.lt_def,rev_val,f] at h
      exact h.trans (s45_rows_orthonormal r s n)
    · have hz (j : Fin (n+1)) : s45 s n j.val=0 :=
        s45_outside s n j.val (Or.inl (Nat.lt_of_not_ge hsn))
      have hn : ¬(r=s ∧ r≤n) := by rintro ⟨rfl,hrn⟩; exact hsn hrn
      simp only [hz,mul_zero,ite_self,Finset.sum_const_zero,if_neg hn]
  · have hz (j : Fin (n+1)) : s45 r n j.val=0 :=
      s45_outside r n j.val (Or.inl (Nat.lt_of_not_ge hrn))
    simp only [hz,star_zero,zero_mul,ite_self,Finset.sum_const_zero,mul_zero,
      hrn,and_false,if_false]

#print axioms s45_rows_orthonormal
#print axioms s45_row_norm_extended
#print axioms s45_odd_half_rows
end TorusLean.Shared.FermionLocalJet.FourCoupling
