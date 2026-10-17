import torus.shared.FermionLocalJetFourCouplingRowMatrix

/-! Full fixed-total-degree orthogonality of the original two-stage F-S
transformation. Both relative degree D and odd spectator copy r are retained;
the previously verified highest-weight rows are only the T=D slice. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators ComplexConjugate

private theorem s45_row_inner_extended (z w n M : ℕ) (hn : n≤M) :
    (∑ p : Fin (M+1), star (s45 z n p.val) * s45 w n p.val) =
      if z=w ∧ z≤n then 1 else 0 := by
  let f : ℕ → ℂ := fun p => star (s45 z n p) * s45 w n p
  have he : (∑ p ∈ Finset.range (M+1), f p) = ∑ p ∈ Finset.range (n+1), f p := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro p hp hnot
    have hout : n<p := by simp only [Finset.mem_range] at hnot; omega
    simp only [f,s45_outside z n p (Or.inr hout),star_zero,zero_mul]
  rw [Fin.sum_univ_eq_sum_range (fun p => star (s45 z n p) * s45 w n p) (M+1)]
  change (∑ p ∈ Finset.range (M+1), f p) = _
  rw [he]
  change (∑ p ∈ Finset.range (n+1), star (s45 z n p) * s45 w n p) = _
  rw [← Fin.sum_univ_eq_sum_range (fun p => star (s45 z n p) * s45 w n p) (n+1)]
  exact s45_rows_orthonormal z w n

/-- Every original COM descendant row, on the genuine j<k input coordinates.
No independence or orthogonality of the subsequent exterior images is used. -/
theorem paperS45_rows_orthonormal (D E T r s : ℕ)
    (hD : D≤T) (hE : E≤T) (hr : r≤D) (hs : s≤E) (hro : Odd r) (hso : Odd s) :
    (∑ p : Fin (T+1), ∑ j : Fin (T-p.val+1), if j.val<T-p.val-j.val then
      star (paperS45 r D T p.val j.val (T-p.val-j.val)) *
        paperS45 s E T p.val j.val (T-p.val-j.val) else 0) =
      if D=E ∧ r=s then 1 else 0 := by
  classical
  have hsqrt : (Real.sqrt (2:ℝ):ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have he (p : Fin (T+1)) :
      (∑ j : Fin (T-p.val+1), if j.val<T-p.val-j.val then
        star (paperS45 r D T p.val j.val (T-p.val-j.val)) *
          paperS45 s E T p.val j.val (T-p.val-j.val) else 0) =
      (star (s45 (D-r) (T-r) p.val) * s45 (E-s) (T-s) p.val) *
        (if r=s ∧ r≤T-p.val then 1 else 0) := by
    calc
      _ = (star (s45 (D-r) (T-r) p.val) * s45 (E-s) (T-s) p.val) *
          (2 * ∑ j : Fin (T-p.val+1), if j.val<T-p.val-j.val then
            star (s45 r (T-p.val) j.val) * s45 s (T-p.val) j.val else 0) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have ht : p.val+j.val+(T-p.val-j.val)=T := by
          have := p.isLt; have := j.isLt; omega
        have hn : j.val+(T-p.val-j.val)=T-p.val := by
          have := j.isLt; omega
        simp only [paperS45,hr,hs,hD,hE,ht,and_self,if_true,hn]
        split_ifs
        · simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
          calc
            _ = (Real.sqrt (2:ℝ):ℂ)^2 *
                (conj (s45 (D-r) (T-r) p.val) * s45 (E-s) (T-s) p.val) *
                (conj (s45 r (T-p.val) j.val) * s45 s (T-p.val) j.val) := by ring
            _ = _ := by rw [hsqrt]; ring
        · simp
      _ = _ := by rw [s45_odd_half_rows r s (T-p.val) hro hso]
  simp_rw [he]
  by_cases hrs : r=s
  · subst s
    have hp (p : Fin (T+1)) :
        (star (s45 (D-r) (T-r) p.val) * s45 (E-r) (T-r) p.val) *
          (if r=r ∧ r≤T-p.val then 1 else 0) =
        star (s45 (D-r) (T-r) p.val) * s45 (E-r) (T-r) p.val := by
      by_cases h : r≤T-p.val
      · simp [h]
      · have hout : T-r<p.val := by have := p.isLt; omega
        simp only [s45_outside (D-r) (T-r) p.val (Or.inr hout),star_zero,zero_mul]
    calc
      _ = ∑ p : Fin (T+1), star (s45 (D-r) (T-r) p.val) * s45 (E-r) (T-r) p.val :=
        Finset.sum_congr rfl (fun p _ => hp p)
      _ = _ := by
        rw [s45_row_inner_extended (D-r) (E-r) (T-r) T (Nat.sub_le T r)]
        have hz : D-r≤T-r := by omega
        have heq : D-r=E-r ↔ D=E := by omega
        simp only [hz,and_true,heq]
  · simp [hrs]

#print axioms paperS45_rows_orthonormal
end TorusLean.Shared.FermionLocalJet.FourCoupling
