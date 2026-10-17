import torus.shared.BosonFiniteCertificateNatMixedComparison

/-! The source comparison with precisely the degree-at-most-eight delta term.
The old all-degree delta-H comparison is not used to pay a finite thermal
budget. Above degree eight the true H-square-minus-H coefficient is retained
without delta; the odd rank correction cancels it exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

/-- Genuine finite weighted-degree projection, applied before the original H. -/
def natLowDegreeProjection : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  ∑ d ∈ Finset.range 9, natOrbitalComponent d

def canonicalNatCutoffComparisonForm (f g : Core ℕ ℂ) : ℂ :=
  natOccupationInner f (canonicalPairHamiltonianNat (canonicalPairHamiltonianNat g)) -
    natOccupationInner f (canonicalPairHamiltonianNat g) - canonicalNatOriginalCOMForm f g +
      (delta : ℂ) * natOccupationInner f (canonicalPairHamiltonianNat (natLowDegreeProjection g))

theorem natLowDegreeProjection_weighted (d : ℕ) (f : Core ℕ ℂ)
    (hd : f.IsWeightedHomogeneous id d) :
    natLowDegreeProjection f = if d ≤ 8 then f else 0 := by
  simp only [natLowDegreeProjection, LinearMap.sum_apply, natOrbitalComponent,
    MvPolynomial.weightedHomogeneousComponent_of_mem hd]
  by_cases hlow : d ≤ 8
  · have hm : d ∈ Finset.range 9 := Finset.mem_range.mpr (by omega)
    simp [hm, hlow]
  · have hm : d ∉ Finset.range 9 := by simp only [Finset.mem_range]; omega
    simp [hm, hlow]

/-- The delta term is exactly a finite sum of the original nonunit relative
ranks, with no unweighted all-degree relative-H series hidden in it. -/
theorem canonicalPairHamiltonianNat_lowProjection_relative (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hL : canonicalCOMLowerNat f = 0) :
    canonicalPairHamiltonianNat (natLowDegreeProjection f) =
      ∑ d ∈ Finset.range 9, natOccupationInner (w3RelativeSeed d) f • w3RelativeSeed d := by
  rw [natLowDegreeProjection, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [canonicalPairHamiltonianNat_relative_rank_action d (natOrbitalComponent d f)
    (natOrbitalComponent_particle 3 d f hN) (natOrbitalComponent_weighted d f)
    (natOrbitalComponent_lower_kernel d f hL),
    natOccupationInner_orbitalComponent_right d (w3RelativeSeed d) f
      (w3RelativeSeed_bihomogeneous d).2]

theorem canonicalNatCutoffComparisonForm_low_eq_original (d : ℕ) (f g : Core ℕ ℂ)
    (hd : g.IsWeightedHomogeneous id d) (hlo : d ≤ 8) :
    canonicalNatCutoffComparisonForm f g = canonicalNatInfiniteComparisonForm f g := by
  unfold canonicalNatCutoffComparisonForm canonicalNatInfiniteComparisonForm
  rw [natLowDegreeProjection_weighted d g hd, if_pos hlo]

theorem canonicalNatCutoffComparisonForm_relative_cross_weight_zero (d e : ℕ)
    (f g : Core ℕ ℂ) (hNf : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (he : g.IsWeightedHomogeneous id e)
    (hLg : canonicalCOMLowerNat g = 0) (hde : d ≠ e) :
    canonicalNatCutoffComparisonForm f g = 0 := by
  unfold canonicalNatCutoffComparisonForm
  rw [canonicalPairHamiltonianNat_relative_square_cross_weight_zero d e f g hd hNg he hLg hde,
    canonicalPairHamiltonianNat_relative_cross_weight_zero d e f g hd hNg he hLg hde,
    canonicalNatOriginalCOMForm_cross_weight_zero d e f g hNf hd hNg he hde,
    natLowDegreeProjection_weighted e g he]
  split_ifs
  · rw [canonicalPairHamiltonianNat_relative_cross_weight_zero d e f g hd hNg he hLg hde]
    ring
  · simp only [map_zero, natOccupationInner_zero_right, mul_zero, sub_self, add_zero]

theorem canonicalNatCutoffComparisonForm_high_relative (d : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id d)
    (hLg : canonicalCOMLowerNat g = 0) (hhigh : 9 ≤ d) :
    canonicalNatCutoffComparisonForm f g =
      (2*(-1/2:ℂ)^d) *
        (star (natOccupationInner (w3RelativeSeed d) f) * natOccupationInner (w3RelativeSeed d) g) := by
  unfold canonicalNatCutoffComparisonForm
  rw [natLowDegreeProjection_weighted d g hdg, if_neg (show ¬d ≤ 8 by omega),
    map_zero, natOccupationInner_zero_right,
    canonicalNatOriginalCOMForm_high_zero d f g hNf hdf hNg hdg hhigh,
    canonicalPairHamiltonianNat_relative_square_action d g hNg hdg hLg,
    canonicalPairHamiltonianNat_relative_rank_action d g hNg hdg hLg]
  simp only [natOccupationInner_smul_right, natOccupationInner_conj_symm]
  ring

theorem canonicalNatCutoffComparisonForm_high_relative_re (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f = 0) (hhigh : 9 ≤ d) :
    (canonicalNatCutoffComparisonForm f f).re =
      (2*(-1/2:ℝ)^d) * Complex.normSq (natOccupationInner (w3RelativeSeed d) f) := by
  rw [canonicalNatCutoffComparisonForm_high_relative d f f hN hd hN hd hL hhigh]
  have hc : star (natOccupationInner (w3RelativeSeed d) f) * natOccupationInner (w3RelativeSeed d) f =
      (Complex.normSq (natOccupationInner (w3RelativeSeed d) f) : ℂ) :=
    Complex.normSq_eq_conj_mul_self.symm
  rw [hc]
  have he : (2*(-1/2:ℂ)^d) = ((2*(-1/2:ℝ)^d : ℝ) : ℂ) := by
    push_cast <;> rfl
  rw [he, ←Complex.ofReal_mul, Complex.ofReal_re]

/-- At high odd degree the correction leaves exactly zero, with no delta-H
remainder to be paid by a finite thermal budget. -/
theorem canonicalNatCutoffComparisonForm_add_odd_tail_nonneg (d : ℕ)
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f = 0) :
    0 ≤ (canonicalNatCutoffComparisonForm f f).re + natOddRelativeTail d f := by
  by_cases hlow : d ≤ 8
  · rw [canonicalNatCutoffComparisonForm_low_eq_original d f f hd hlow]
    exact canonicalNatInfiniteComparisonForm_add_odd_tail_nonneg d f hN hd hL
  have hhigh : 9 ≤ d := by omega
  rw [canonicalNatCutoffComparisonForm_high_relative_re d f hN hd hL hhigh]
  by_cases hodd : Odd d
  · rw [natOddRelativeTail, if_pos ⟨hodd,hhigh⟩,
      show (-1/2:ℝ)=-(1/2:ℝ) by ring, hodd.neg_pow]
    convert (le_refl (0 : ℝ)) using 1 <;> ring
  · have heven := Nat.not_odd_iff_even.mp hodd
    rw [natOddRelativeTail, if_neg (not_and_of_not_left _ hodd), add_zero,
      show (-1/2:ℝ)=-(1/2:ℝ) by ring, heven.neg_pow]
    exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)

#print axioms canonicalPairHamiltonianNat_lowProjection_relative
#print axioms canonicalNatCutoffComparisonForm_high_relative
#print axioms canonicalNatCutoffComparisonForm_add_odd_tail_nonneg
end TorusLean.BosonFiniteCertificate
