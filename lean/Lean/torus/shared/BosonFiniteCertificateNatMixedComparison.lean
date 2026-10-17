import torus.shared.BosonFiniteCertificateNatMixedComparisonCOM
import torus.shared.BosonFiniteCertificateNatDegreeOrthogonalityRows

/-! The actual corrected comparison on arbitrary finite Nat relative cores.
Cross-degree terms are proved zero for the original operators, the original
COM tsum is independently proved convergent, and genuine weighted components
preserve the lowering kernel. No block-diagonal or positivity premise is used.
This remains a polynomial source result, before physical torus transfer. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

private theorem natM3_add_left (f g h : Core ℕ ℂ) :
    canonicalNatOriginalM3Form (f+g) h = canonicalNatOriginalM3Form f h + canonicalNatOriginalM3Form g h := by
  unfold canonicalNatOriginalM3Form canonicalNatRowChannelForm
  simp only [map_add, natOccupationInner_add_left]
  simp_rw [add_sub_add_comm]
  simp only [Finset.sum_add_distrib]

private theorem natM3_add_right (f g h : Core ℕ ℂ) :
    canonicalNatOriginalM3Form f (g+h) = canonicalNatOriginalM3Form f g + canonicalNatOriginalM3Form f h := by
  unfold canonicalNatOriginalM3Form canonicalNatRowChannelForm
  simp only [map_add, natOccupationInner_add_right]
  simp_rw [add_sub_add_comm]
  simp only [Finset.sum_add_distrib]

private theorem natM3_zero_left (f : Core ℕ ℂ) : canonicalNatOriginalM3Form 0 f = 0 := by
  simp [canonicalNatOriginalM3Form, canonicalNatRowChannelForm, natOccupationInner_zero_left]

private theorem natM3_zero_right (f : Core ℕ ℂ) : canonicalNatOriginalM3Form f 0 = 0 := by
  simp [canonicalNatOriginalM3Form, canonicalNatRowChannelForm, natOccupationInner_zero_right]

theorem canonicalNatOriginalM3Form_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → Core ℕ ℂ) (g : Core ℕ ℂ) :
    canonicalNatOriginalM3Form (∑ i ∈ s, f i) g = ∑ i ∈ s, canonicalNatOriginalM3Form (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, natM3_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, natM3_add_left, ih]

theorem canonicalNatOriginalM3Form_sum_right {ι : Type*} (s : Finset ι)
    (f : Core ℕ ℂ) (g : ι → Core ℕ ℂ) :
    canonicalNatOriginalM3Form f (∑ i ∈ s, g i) = ∑ i ∈ s, canonicalNatOriginalM3Form f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, natM3_zero_right]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, natM3_add_right, ih]

theorem canonicalNatOriginalCOMTerm_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → Core ℕ ℂ) (g : Core ℕ ℂ) (n : ℕ) :
    canonicalNatOriginalCOMTerm (∑ i ∈ s, f i) g n = ∑ i ∈ s, canonicalNatOriginalCOMTerm (f i) g n := by
  simp only [canonicalNatOriginalCOMTerm, canonicalCOMRaiseNat_iterate_sum,
    canonicalNatOriginalM3Form_sum_left, Finset.mul_sum]

theorem canonicalNatOriginalCOMTerm_sum_right {ι : Type*} (s : Finset ι)
    (f : Core ℕ ℂ) (g : ι → Core ℕ ℂ) (n : ℕ) :
    canonicalNatOriginalCOMTerm f (∑ i ∈ s, g i) n = ∑ i ∈ s, canonicalNatOriginalCOMTerm f (g i) n := by
  simp only [canonicalNatOriginalCOMTerm, canonicalCOMRaiseNat_iterate_sum,
    canonicalNatOriginalM3Form_sum_right, Finset.mul_sum]

theorem canonicalNatOriginalCOMForm_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → Core ℕ ℂ) (g : Core ℕ ℂ)
    (hNf : ∀ i ∈ s, (f i).IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    canonicalNatOriginalCOMForm (∑ i ∈ s, f i) g = ∑ i ∈ s, canonicalNatOriginalCOMForm (f i) g := by
  have hNs : (∑ i ∈ s, f i).IsHomogeneous 3 :=
    (MvPolynomial.homogeneousSubmodule ℕ ℂ 3).sum_mem hNf
  rw [canonicalNatOriginalCOMForm_eq_sum_nine _ g hNs hNg]
  simp only [canonicalNatOriginalCOMTerm_sum_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact (canonicalNatOriginalCOMForm_eq_sum_nine (f i) g (hNf i hi) hNg).symm

theorem canonicalNatOriginalCOMForm_sum_right {ι : Type*} (s : Finset ι)
    (f : Core ℕ ℂ) (g : ι → Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : ∀ i ∈ s, (g i).IsHomogeneous 3) :
    canonicalNatOriginalCOMForm f (∑ i ∈ s, g i) = ∑ i ∈ s, canonicalNatOriginalCOMForm f (g i) := by
  have hNs : (∑ i ∈ s, g i).IsHomogeneous 3 :=
    (MvPolynomial.homogeneousSubmodule ℕ ℂ 3).sum_mem hNg
  rw [canonicalNatOriginalCOMForm_eq_sum_nine f _ hNf hNs]
  simp only [canonicalNatOriginalCOMTerm_sum_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact (canonicalNatOriginalCOMForm_eq_sum_nine f (g i) hNf (hNg i hi)).symm

theorem canonicalNatInfiniteComparisonForm_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → Core ℕ ℂ) (g : Core ℕ ℂ)
    (hNf : ∀ i ∈ s, (f i).IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    canonicalNatInfiniteComparisonForm (∑ i ∈ s, f i) g =
      ∑ i ∈ s, canonicalNatInfiniteComparisonForm (f i) g := by
  simp only [canonicalNatInfiniteComparisonForm, natOccupationInner_sum_left,
    canonicalNatOriginalCOMForm_sum_left s f g hNf hNg, Finset.mul_sum,
    ←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]

theorem canonicalNatInfiniteComparisonForm_sum_right {ι : Type*} (s : Finset ι)
    (f : Core ℕ ℂ) (g : ι → Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : ∀ i ∈ s, (g i).IsHomogeneous 3) :
    canonicalNatInfiniteComparisonForm f (∑ i ∈ s, g i) =
      ∑ i ∈ s, canonicalNatInfiniteComparisonForm f (g i) := by
  simp only [canonicalNatInfiniteComparisonForm, map_sum, natOccupationInner_sum_right,
    canonicalNatOriginalCOMForm_sum_right s f g hNf hNg, Finset.mul_sum,
    ←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]

/-- This diagonalization is proved from the actual cross-degree identities. -/
theorem canonicalNatInfiniteComparisonForm_orbital_diagonal (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hL : canonicalCOMLowerNat f=0) :
    canonicalNatInfiniteComparisonForm f f =
      ∑ d ∈ f.support.image (Finsupp.weight id),
        canonicalNatInfiniteComparisonForm (natOrbitalComponent d f) (natOrbitalComponent d f) := by
  classical
  have hleft := canonicalNatInfiniteComparisonForm_sum_left
    (f.support.image (Finsupp.weight id)) (fun d => natOrbitalComponent d f) f
    (fun d _ => natOrbitalComponent_particle 3 d f hN) hN
  rw [natOrbitalComponent_finite_sum] at hleft
  rw [hleft]
  apply Finset.sum_congr rfl
  intro d hd
  have hright := canonicalNatInfiniteComparisonForm_sum_right
    (f.support.image (Finsupp.weight id)) (natOrbitalComponent d f) (fun e => natOrbitalComponent e f)
    (natOrbitalComponent_particle 3 d f hN) (fun e _ => natOrbitalComponent_particle 3 e f hN)
  rw [natOrbitalComponent_finite_sum] at hright
  rw [hright, Finset.sum_eq_single d]
  · intro e he hed
    exact canonicalNatInfiniteComparisonForm_relative_cross_weight_zero d e _ _
      (natOrbitalComponent_particle 3 d f hN) (natOrbitalComponent_weighted d f)
      (natOrbitalComponent_particle 3 e f hN) (natOrbitalComponent_weighted e f)
      (natOrbitalComponent_lower_kernel e f hL) (Ne.symm hed)
  · intro hnot
    exact (hnot hd).elim

theorem natOccupationInner_orbitalComponent_right (d : ℕ) (f g : Core ℕ ℂ)
    (hd : f.IsWeightedHomogeneous id d) :
    natOccupationInner f (natOrbitalComponent d g) = natOccupationInner f g := by
  classical
  unfold natOccupationInner Finsupp.sum
  apply Finset.sum_congr rfl
  intro n hn
  have hw := hd (Finsupp.mem_support_iff.mp hn)
  change (natOccupationWeight n : ℂ) * star (f.coeff n) * (natOrbitalComponent d g).coeff n = _
  simp [natOrbitalComponent, MvPolynomial.coeff_weightedHomogeneousComponent, hw]

theorem natOddRelativeTail_orbitalComponent (d : ℕ) (f : Core ℕ ℂ) :
    natOddRelativeTail d (natOrbitalComponent d f) = natOddRelativeTail d f := by
  unfold natOddRelativeTail
  rw [natOccupationInner_orbitalComponent_right d (w3RelativeSeed d) f
    (w3RelativeSeed_bihomogeneous d).2]

/-- The finite total of the original odd-rank coefficients on this input. -/
def natOddRelativeTailTotal (f : Core ℕ ℂ) : ℝ :=
  ∑ d ∈ f.support.image (Finsupp.weight id), natOddRelativeTail d f

/-- The actual comparison for every finite-support N3 relative polynomial,
with mixed orbital degrees allowed and no comparison positivity premise. -/
theorem canonicalNatInfiniteComparisonForm_add_odd_tail_total_nonneg
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hL : canonicalCOMLowerNat f=0) :
    0 ≤ (canonicalNatInfiniteComparisonForm f f).re + natOddRelativeTailTotal f := by
  rw [canonicalNatInfiniteComparisonForm_orbital_diagonal f hN hL]
  simp only [Complex.re_sum, natOddRelativeTailTotal, ←Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro d hd
  rw [←natOddRelativeTail_orbitalComponent d f]
  exact canonicalNatInfiniteComparisonForm_add_odd_tail_nonneg d (natOrbitalComponent d f)
    (natOrbitalComponent_particle 3 d f hN) (natOrbitalComponent_weighted d f)
    (natOrbitalComponent_lower_kernel d f hL)

#print axioms canonicalNatInfiniteComparisonForm_orbital_diagonal
#print axioms natOddRelativeTail_orbitalComponent
#print axioms canonicalNatInfiniteComparisonForm_add_odd_tail_total_nonneg
end TorusLean.BosonFiniteCertificate
