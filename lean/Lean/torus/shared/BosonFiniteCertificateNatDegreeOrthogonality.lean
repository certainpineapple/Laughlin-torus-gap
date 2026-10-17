import torus.shared.BosonFiniteCertificateNatTailCorrectedComparison

/-! Actual cross-degree orthogonality for the factorial-weighted Nat core.
The relative H and genuine H-squared cross terms vanish by their already
proved full-core rank actions. No block-diagonal comparison is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

/-- Different actual orbital weights have disjoint coefficient supports. -/
theorem natOccupationInner_eq_zero_of_weight_ne (d e : ℕ) (f g : Core ℕ ℂ)
    (hd : f.IsWeightedHomogeneous id d) (he : g.IsWeightedHomogeneous id e)
    (hde : d ≠ e) : natOccupationInner f g = 0 := by
  classical
  unfold natOccupationInner Finsupp.sum
  apply Finset.sum_eq_zero
  intro n hn
  have hfn : f.coeff n ≠ 0 := Finsupp.mem_support_iff.mp hn
  have hgn : g.coeff n = 0 := he.coeff_eq_zero n (by rw [hd hfn]; exact hde)
  change (natOccupationWeight n : ℂ) * star (f.coeff n) * g.coeff n = 0
  rw [hgn, mul_zero]

theorem natOccupationInner_relativeSeed_eq_zero_of_weight_ne
    (d e : ℕ) (f : Core ℕ ℂ) (hd : f.IsWeightedHomogeneous id d) (hde : d ≠ e) :
    natOccupationInner f (w3RelativeSeed e) = 0 :=
  natOccupationInner_eq_zero_of_weight_ne d e f (w3RelativeSeed e)
    hd (w3RelativeSeed_bihomogeneous e).2 hde

/-- The left input need not itself be relative or three-particle. -/
theorem canonicalPairHamiltonianNat_relative_cross_weight_zero
    (d e : ℕ) (f g : Core ℕ ℂ) (hd : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (he : g.IsWeightedHomogeneous id e)
    (hLg : canonicalCOMLowerNat g = 0) (hde : d ≠ e) :
    natOccupationInner f (canonicalPairHamiltonianNat g) = 0 := by
  rw [canonicalPairHamiltonianNat_relative_rank_action e g hNg he hLg,
    natOccupationInner_smul_right,
    natOccupationInner_relativeSeed_eq_zero_of_weight_ne d e f hd hde, mul_zero]

/-- This uses the true composition H(Hg), not a separately defined square. -/
theorem canonicalPairHamiltonianNat_relative_square_cross_weight_zero
    (d e : ℕ) (f g : Core ℕ ℂ) (hd : f.IsWeightedHomogeneous id d)
    (hNg : g.IsHomogeneous 3) (he : g.IsWeightedHomogeneous id e)
    (hLg : canonicalCOMLowerNat g = 0) (hde : d ≠ e) :
    natOccupationInner f (canonicalPairHamiltonianNat (canonicalPairHamiltonianNat g)) = 0 := by
  rw [canonicalPairHamiltonianNat_relative_square_action e g hNg he hLg,
    natOccupationInner_smul_right,
    natOccupationInner_relativeSeed_eq_zero_of_weight_ne d e f hd hde, mul_zero]

#print axioms natOccupationInner_eq_zero_of_weight_ne
#print axioms natOccupationInner_relativeSeed_eq_zero_of_weight_ne
#print axioms canonicalPairHamiltonianNat_relative_cross_weight_zero
#print axioms canonicalPairHamiltonianNat_relative_square_cross_weight_zero
end TorusLean.BosonFiniteCertificate
