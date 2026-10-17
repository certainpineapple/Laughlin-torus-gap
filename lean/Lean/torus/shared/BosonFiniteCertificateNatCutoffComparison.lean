import torus.shared.BosonFiniteCertificateNatCutoffComparisonCore

/-! The finite-mixed relative comparison with the paper's delta-H cutoff.
The only delta term is the original H applied after projection to degrees
zero through eight. No full-degree delta-H or torus transfer is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open scoped BigOperators

theorem canonicalNatCutoffComparisonForm_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → Core ℕ ℂ) (g : Core ℕ ℂ)
    (hNf : ∀ i ∈ s, (f i).IsHomogeneous 3) (hNg : g.IsHomogeneous 3) :
    canonicalNatCutoffComparisonForm (∑ i ∈ s, f i) g =
      ∑ i ∈ s, canonicalNatCutoffComparisonForm (f i) g := by
  simp only [canonicalNatCutoffComparisonForm, natOccupationInner_sum_left,
    canonicalNatOriginalCOMForm_sum_left s f g hNf hNg, Finset.mul_sum,
    ←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]

theorem canonicalNatCutoffComparisonForm_sum_right {ι : Type*} (s : Finset ι)
    (f : Core ℕ ℂ) (g : ι → Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hNg : ∀ i ∈ s, (g i).IsHomogeneous 3) :
    canonicalNatCutoffComparisonForm f (∑ i ∈ s, g i) =
      ∑ i ∈ s, canonicalNatCutoffComparisonForm f (g i) := by
  simp only [canonicalNatCutoffComparisonForm, map_sum, natOccupationInner_sum_right,
    canonicalNatOriginalCOMForm_sum_right s f g hNf hNg, Finset.mul_sum,
    ←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]

/-- This diagonalization is proved from the actual cross-degree identities. -/
theorem canonicalNatCutoffComparisonForm_orbital_diagonal (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hL : canonicalCOMLowerNat f=0) :
    canonicalNatCutoffComparisonForm f f =
      ∑ d ∈ f.support.image (Finsupp.weight id),
        canonicalNatCutoffComparisonForm (natOrbitalComponent d f) (natOrbitalComponent d f) := by
  classical
  have hleft := canonicalNatCutoffComparisonForm_sum_left
    (f.support.image (Finsupp.weight id)) (fun d => natOrbitalComponent d f) f
    (fun d _ => natOrbitalComponent_particle 3 d f hN) hN
  rw [natOrbitalComponent_finite_sum] at hleft
  rw [hleft]
  apply Finset.sum_congr rfl
  intro d hd
  have hright := canonicalNatCutoffComparisonForm_sum_right
    (f.support.image (Finsupp.weight id)) (natOrbitalComponent d f) (fun e => natOrbitalComponent e f)
    (natOrbitalComponent_particle 3 d f hN) (fun e _ => natOrbitalComponent_particle 3 e f hN)
  rw [natOrbitalComponent_finite_sum] at hright
  rw [hright, Finset.sum_eq_single d]
  · intro e he hed
    exact canonicalNatCutoffComparisonForm_relative_cross_weight_zero d e _ _
      (natOrbitalComponent_particle 3 d f hN) (natOrbitalComponent_weighted d f)
      (natOrbitalComponent_particle 3 e f hN) (natOrbitalComponent_weighted e f)
      (natOrbitalComponent_lower_kernel e f hL) (Ne.symm hed)
  · intro hnot
    exact (hnot hd).elim

/-- The genuine finite-support relative comparison with exactly the low-degree
paper delta term. The source odd-rank correction retains its original weights. -/
theorem canonicalNatCutoffComparisonForm_add_odd_tail_total_nonneg
    (f : Core ℕ ℂ) (hN : f.IsHomogeneous 3) (hL : canonicalCOMLowerNat f=0) :
    0 ≤ (canonicalNatCutoffComparisonForm f f).re + natOddRelativeTailTotal f := by
  rw [canonicalNatCutoffComparisonForm_orbital_diagonal f hN hL]
  simp only [Complex.re_sum, natOddRelativeTailTotal, ←Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro d hd
  rw [←natOddRelativeTail_orbitalComponent d f]
  exact canonicalNatCutoffComparisonForm_add_odd_tail_nonneg d (natOrbitalComponent d f)
    (natOrbitalComponent_particle 3 d f hN) (natOrbitalComponent_weighted d f)
    (natOrbitalComponent_lower_kernel d f hL)

#print axioms canonicalNatCutoffComparisonForm_orbital_diagonal
#print axioms canonicalNatCutoffComparisonForm_add_odd_tail_total_nonneg
end TorusLean.BosonFiniteCertificate
