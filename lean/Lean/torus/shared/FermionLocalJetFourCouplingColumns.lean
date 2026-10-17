import torus.shared.FermionLocalJetFourCouplingHalf

/-! The original highest-weight S columns in the formal (p,j,k) input space.
Both normalized 45-degree factors are retained, together with the unique
sqrt(2) for the j<k antisymmetric input convention. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators ComplexConjugate

/-- Exact equation F-S, with all indicated range and total-degree restrictions. -/
def paperS45 (r D T p j k : ℕ) : ℂ :=
  if r≤D ∧ D≤T ∧ p+j+k=T then
    (Real.sqrt (2:ℝ):ℂ) * s45 r (j+k) j * s45 (D-r) (T-r) p
  else 0

def highestOrderedCoefficient (D r p j : ℕ) : ℂ :=
  s45 r (D-p) j * s45 (D-r) (D-r) p

def highestS45 (D r p j : ℕ) : ℂ :=
  (Real.sqrt (2:ℝ):ℂ) * highestOrderedCoefficient D r p j

theorem highestS45_eq_paper (D r : ℕ) (hr : r≤D)
    (p : Fin (D+1)) (j : Fin (D-p.val+1)) :
    highestS45 D r p.val j.val = paperS45 r D D p.val j.val (D-p.val-j.val) := by
  have hp := p.isLt
  have hj := j.isLt
  have ht : p.val+j.val+(D-p.val-j.val)=D := by omega
  have hn : j.val+(D-p.val-j.val)=D-p.val := by omega
  simp only [paperS45,hr,le_refl,ht,and_self,if_true,hn,highestS45,highestOrderedCoefficient]
  ring

theorem highestS45_star (D r p j : ℕ) : star (highestS45 D r p j) = highestS45 D r p j := by
  simp only [highestS45,highestOrderedCoefficient,star_mul,s45_star,
    Complex.star_def,Complex.conj_ofReal]
  ring

/-- The complete ordered (p,j,k) input keeps every multiplicity. -/
theorem highestOrderedCoefficient_rows (D r s : ℕ) (hr : r≤D) (hs : s≤D) :
    (∑ p : Fin (D+1), ∑ j : Fin (D-p.val+1),
      star (highestOrderedCoefficient D r p.val j.val) *
        highestOrderedCoefficient D s p.val j.val) = if r=s then 1 else 0 := by
  classical
  have he (p : Fin (D+1)) :
      (∑ j : Fin (D-p.val+1), star (highestOrderedCoefficient D r p.val j.val) *
        highestOrderedCoefficient D s p.val j.val) =
      (star (s45 (D-r) (D-r) p.val) * s45 (D-s) (D-s) p.val) *
        (if r=s ∧ r≤D-p.val then 1 else 0) := by
    rw [← s45_rows_orthonormal r s (D-p.val),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [highestOrderedCoefficient,star_mul]
    ring
  simp_rw [he]
  by_cases hrs : r=s
  · subst s
    have hp (p : Fin (D+1)) :
        (star (s45 (D-r) (D-r) p.val) * s45 (D-r) (D-r) p.val) *
          (if r=r ∧ r≤D-p.val then 1 else 0) =
        star (s45 (D-r) (D-r) p.val) * s45 (D-r) (D-r) p.val := by
      by_cases h : r≤D-p.val
      · simp [h]
      · have hout : D-r<p.val := by have := p.isLt; omega
        simp only [s45_outside (D-r) (D-r) p.val (Or.inr hout),star_zero,zero_mul]
    calc
      _ = ∑ p : Fin (D+1), star (s45 (D-r) (D-r) p.val) * s45 (D-r) (D-r) p.val :=
        Finset.sum_congr rfl (fun p _ => hp p)
      _ = _ := by simpa using s45_row_norm_extended (D-r) (D-r) D le_rfl (Nat.sub_le D r)
  · simp [hrs]

/-- Actual odd-copy S columns are orthonormal on j<k. The sqrt(2) is
cancelled exactly by the spectator half-space identity, without a missing
factor two or an assumed nonzero physical wedge image. -/
theorem highestS45_odd_rows (D r s : ℕ) (hr : r≤D) (hs : s≤D)
    (hro : Odd r) (hso : Odd s) :
    (∑ p : Fin (D+1), ∑ j : Fin (D-p.val+1), if j.val<D-p.val-j.val then
      star (highestS45 D r p.val j.val) * highestS45 D s p.val j.val else 0) =
      if r=s then 1 else 0 := by
  classical
  have hsqrt : (Real.sqrt (2:ℝ):ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have he (p : Fin (D+1)) :
      (∑ j : Fin (D-p.val+1), if j.val<D-p.val-j.val then
        star (highestS45 D r p.val j.val) * highestS45 D s p.val j.val else 0) =
      ∑ j : Fin (D-p.val+1), star (highestOrderedCoefficient D r p.val j.val) *
        highestOrderedCoefficient D s p.val j.val := by
    calc
      _ = (star (s45 (D-r) (D-r) p.val) * s45 (D-s) (D-s) p.val) *
          (2 * ∑ j : Fin (D-p.val+1), if j.val<D-p.val-j.val then
            star (s45 r (D-p.val) j.val) * s45 s (D-p.val) j.val else 0) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs
        · simp only [highestS45,highestOrderedCoefficient,star_mul,
            Complex.star_def,Complex.conj_ofReal]
          calc
            _ = (Real.sqrt (2:ℝ):ℂ)^2 *
                (conj (s45 (D-r) (D-r) p.val) * s45 (D-s) (D-s) p.val) *
                (conj (s45 r (D-p.val) j.val) * s45 s (D-p.val) j.val) := by ring
            _ = _ := by rw [hsqrt]; ring
        · simp
      _ = (star (s45 (D-r) (D-r) p.val) * s45 (D-s) (D-s) p.val) *
          (∑ j : Fin (D-p.val+1), star (s45 r (D-p.val) j.val) * s45 s (D-p.val) j.val) := by
        rw [s45_odd_half_rows r s (D-p.val) hro hso,s45_rows_orthonormal]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [highestOrderedCoefficient,star_mul]
        ring
  simp_rw [he]
  exact highestOrderedCoefficient_rows D r s hr hs

#print axioms highestS45_eq_paper
#print axioms highestS45_star
#print axioms highestOrderedCoefficient_rows
#print axioms highestS45_odd_rows
end TorusLean.Shared.FermionLocalJet.FourCoupling
