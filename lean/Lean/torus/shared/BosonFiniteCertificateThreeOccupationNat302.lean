import torus.shared.BosonFiniteCertificateThreeOccupationComplete302
import torus.shared.BosonFiniteCertificateThreeOccupationNatCore
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.Shared.BosonFiniteCertificateCoordinate

theorem k302_nat_occupation_exhaustive (n : ℕ →₀ ℕ) (hN : n.degree = 3)
    (hd : Finsupp.weight id n = 2) :
    ∃ i, (k302occ i).mapDomain Fin.val = n := by
  obtain ⟨v,hvN,hvd,hv⟩ := nat_three_occupation_lift 2 (by decide) n hN hd
  obtain ⟨i,hi⟩ := k302_occupation_exhaustive v hvN hvd
  exact ⟨i,by rw [hi,hv]⟩

/-- Arbitrary Nat-orbital homogeneous three-particle polynomials at degree
2 are actual renames of the original finite canonical source block. -/
theorem k302_nat_homogeneous_block (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 2) :
    ∃ x, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k302occ x) = f := by
  apply polynomial_eq_rename_canonicalBlock k302occ k302_occupation_injective f
  intro n hn
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree = 3 := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  exact k302_nat_occupation_exhaustive n hdeg (hd hc)

#print axioms k302_nat_occupation_exhaustive
#print axioms k302_nat_homogeneous_block
end TorusLean.BosonFiniteCertificate
