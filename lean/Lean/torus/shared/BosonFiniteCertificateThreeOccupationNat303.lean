import torus.shared.BosonFiniteCertificateThreeOccupationComplete303
import torus.shared.BosonFiniteCertificateThreeOccupationNatCore
set_option autoImplicit false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.Shared.BosonFiniteCertificateCoordinate

theorem k303_nat_occupation_exhaustive (n : ℕ →₀ ℕ) (hN : n.degree = 3)
    (hd : Finsupp.weight id n = 3) :
    ∃ i, (k303occ i).mapDomain Fin.val = n := by
  obtain ⟨v,hvN,hvd,hv⟩ := nat_three_occupation_lift 3 (by decide) n hN hd
  obtain ⟨i,hi⟩ := k303_occupation_exhaustive v hvN hvd
  exact ⟨i,by rw [hi,hv]⟩

/-- Arbitrary Nat-orbital homogeneous three-particle polynomials at degree
3 are actual renames of the original finite canonical source block. -/
theorem k303_nat_homogeneous_block (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id 3) :
    ∃ x, MvPolynomial.rename Fin.val
      (canonicalBlock (factorialScale 8) k303occ x) = f := by
  apply polynomial_eq_rename_canonicalBlock k303occ k303_occupation_injective f
  intro n hn
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have hdeg : n.degree = 3 := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  exact k303_nat_occupation_exhaustive n hdeg (hd hc)

#print axioms k303_nat_occupation_exhaustive
#print axioms k303_nat_homogeneous_block
end TorusLean.BosonFiniteCertificate
