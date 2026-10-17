import torus.shared.FermionCertificateThreeCell

/-! Finite support and exact aggregation of the original seven physical rows.
The cutoff 15 is derived from the original t<=7 and auxiliary i<=8. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open scoped BigOperators

theorem certificate_row_t_le : ∀ r : CertificateRow, (certificateRowData r).1 ≤ 7 := by
  decide +kernel

theorem sThree_zero_above (z T p : ℕ) (h : T<z) : sThree z T p=0 := by
  simp only [sThree,integerCoupling,if_neg (by omega : ¬(z≤T ∧ p≤T)),Int.cast_zero,zero_mul]

theorem rowCoupledCoefficient_zero_outside (r : CertificateRow) (z T : ℕ)
    (h : T<(certificateRowData r).1 ∨ (certificateRowData r).1+8<T) :
    rowCoupledCoefficient r z T=0 := by
  unfold rowCoupledCoefficient
  apply Finset.sum_eq_zero
  intro a ha
  have hs := certificate_row_support r a
  have hn : (certificateEntryData r a).1+(certificateEntryData r a).2.1≠T := by
    unfold certificateJetIndex at hs
    omega
  simp only [if_neg hn]

theorem rowEigenCoefficient_zero_outside (r : CertificateRow) (z T : ℕ)
    (h : T<(certificateRowData r).1 ∨ (certificateRowData r).1+8<T) :
    rowEigenCoefficient r z T=0 := by
  simp only [rowEigenCoefficient,rowCoupledCoefficient_zero_outside r z T h,
    mul_zero,zero_pow (by decide : 2≠0),add_zero]

theorem rowEigenCoefficient_zero_above (r : CertificateRow) (z T : ℕ)
    (h : T<z) : rowEigenCoefficient r z T=0 := by
  have hr : rowCoupledCoefficient r z T=0 := by
    unfold rowCoupledCoefficient
    apply Finset.sum_eq_zero
    intro a ha
    split_ifs <;> simp only [sThree_zero_above z T _ h,mul_zero]
  simp only [rowEigenCoefficient,hr,mul_zero,zero_pow (by decide : 2≠0),add_zero]

theorem threeEigenvalue_eq_full_sum (z : ℕ) :
    threeEigenvalue z=∑ r : CertificateRow, ∑ T ∈ Finset.range 16,
      rowEigenCoefficient r z T := by
  unfold threeEigenvalue
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro T hT
  split_ifs with h
  · rfl
  · have hz : T<z ∨ T<(certificateRowData r).1 := by omega
    rcases hz with hz|ht
    · exact (rowEigenCoefficient_zero_above r z T hz).symm
    · exact (rowEigenCoefficient_zero_outside r z T (Or.inl ht)).symm

private theorem sum_shift_nine {E : Type*} [AddCommMonoid E]
    (t : ℕ) (ht : t≤7) (F : ℕ→E)
    (hF : ∀ T, T<t ∨ t+8<T → F T=0) :
    (∑ i : Fin 9, F (t+i.val))=∑ T ∈ Finset.range 16, F T := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => F (t+i)) 9]
  have hl : (∑ T ∈ Finset.range t, F T)=0 := by
    exact Finset.sum_eq_zero (fun T hT => hF T (Or.inl (Finset.mem_range.mp hT)))
  have he : (∑ T ∈ Finset.range (t+9),F T)=∑ i ∈ Finset.range 9,F (t+i) := by
    rw [Finset.sum_range_add,hl,zero_add]
  rw [← he]
  apply Finset.sum_subset (Finset.range_mono (by omega : t+9≤16))
  intro T hT hn
  exact hF T (Or.inr (by simp only [Finset.mem_range] at hn; omega))

/-- All actual row/auxiliary COM blocks aggregate to the literal e_z formula.
This works for arbitrary complex relative matrix entries, including their kernel. -/
theorem original_three_blocks_aggregate (F : ℕ→ℂ) :
    (∑ r : CertificateRow, ∑ i : Fin 9,
      ∑ z : Fin ((certificateRowData r).1+i.val+1),
        (rowEigenCoefficient r z.val ((certificateRowData r).1+i.val):ℂ)*F z.val)=
      ∑ z ∈ Finset.range 16, (threeEigenvalue z:ℂ)*F z := by
  classical
  have he (r : CertificateRow) (i : Fin 9) :
      (∑ z : Fin ((certificateRowData r).1+i.val+1),
        (rowEigenCoefficient r z.val ((certificateRowData r).1+i.val):ℂ)*F z.val)=
      ∑ z ∈ Finset.range 16,
        (rowEigenCoefficient r z ((certificateRowData r).1+i.val):ℂ)*F z := by
    rw [Fin.sum_univ_eq_sum_range
      (fun z : ℕ => (rowEigenCoefficient r z ((certificateRowData r).1+i.val):ℂ)*F z)
      ((certificateRowData r).1+i.val+1)]
    have ht := certificate_row_t_le r
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro z hz hn
    have hz' : (certificateRowData r).1+i.val<z := by
      simp only [Finset.mem_range] at hn
      omega
    simp only [rowEigenCoefficient_zero_above r z _ hz',Complex.ofReal_zero,zero_mul]
  simp_rw [he]
  have hs (r : CertificateRow) (z : ℕ) :
      (∑ i : Fin 9, (rowEigenCoefficient r z ((certificateRowData r).1+i.val):ℂ)*F z)=
      ∑ T ∈ Finset.range 16, (rowEigenCoefficient r z T:ℂ)*F z := by
    refine sum_shift_nine _ (certificate_row_t_le r)
      (fun T : ℕ => (rowEigenCoefficient r z T:ℂ)*F z) ?_
    intro T hT
    simp only [rowEigenCoefficient_zero_outside r z T hT,Complex.ofReal_zero,zero_mul]
  calc
    _ = ∑ r : CertificateRow, ∑ z ∈ Finset.range 16,
        ∑ i : Fin 9, (rowEigenCoefficient r z ((certificateRowData r).1+i.val):ℂ)*F z := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ = ∑ r : CertificateRow, ∑ z ∈ Finset.range 16,
        ∑ T ∈ Finset.range 16, (rowEigenCoefficient r z T:ℂ)*F z := by simp_rw [hs]
    _ = ∑ z ∈ Finset.range 16, (threeEigenvalue z:ℂ)*F z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      rw [threeEigenvalue_eq_full_sum]
      push_cast
      simp only [Finset.sum_mul]

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
