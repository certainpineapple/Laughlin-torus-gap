import torus.shared.BosonFiniteCertificateThreeOccupationComplete304
import torus.shared.BosonFiniteCertificateThreeOccupationNatCore
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.Shared.BosonFiniteCertificateCoordinate

theorem k304_nat_occupation_exhaustive (n : ℕ →₀ ℕ) (hN : n.degree = 3)
    (hd : Finsupp.weight id n = 4) :
    ∃ i, (k304occ i).mapDomain Fin.val = n := by
  obtain ⟨v,hvN,hvd,hv⟩ := nat_three_occupation_lift 4 (by decide) n hN hd
  obtain ⟨i,hi⟩ := k304_occupation_exhaustive v hvN hvd
  exact ⟨i,by rw [hi,hv]⟩

/-- Arbitrary Nat-orbital homogeneous three-particle polynomials at degree
4 are actual renames of the original finite canonical source block. -/
theorem k304_nat_homogeneous_block (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 4) :
    ∃ x, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k304occ x) = f := by
  apply polynomial_eq_rename_canonicalBlock k304occ k304_occupation_injective f
  intro n hn
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree = 3 := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  exact k304_nat_occupation_exhaustive n hdeg (hd hc)

#print axioms k304_nat_occupation_exhaustive
#print axioms k304_nat_homogeneous_block
end TorusLean.BosonFiniteCertificate
