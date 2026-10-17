import torus.shared.BosonFiniteCertificateThreeOccupationComplete308
import torus.shared.BosonFiniteCertificateThreeOccupationNatCore
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.Shared.BosonFiniteCertificateCoordinate

theorem k308_nat_occupation_exhaustive (n : ℕ →₀ ℕ) (hN : n.degree = 3)
    (hd : Finsupp.weight id n = 8) :
    ∃ i, (k308occ i).mapDomain Fin.val = n := by
  obtain ⟨v,hvN,hvd,hv⟩ := nat_three_occupation_lift 8 (by decide) n hN hd
  obtain ⟨i,hi⟩ := k308_occupation_exhaustive v hvN hvd
  exact ⟨i,by rw [hi,hv]⟩

/-- Arbitrary Nat-orbital homogeneous three-particle polynomials at degree
8 are actual renames of the original finite canonical source block. -/
theorem k308_nat_homogeneous_block (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 8) :
    ∃ x, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k308occ x) = f := by
  apply polynomial_eq_rename_canonicalBlock k308occ k308_occupation_injective f
  intro n hn
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree = 3 := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  exact k308_nat_occupation_exhaustive n hdeg (hd hc)

#print axioms k308_nat_occupation_exhaustive
#print axioms k308_nat_homogeneous_block
end TorusLean.BosonFiniteCertificate
