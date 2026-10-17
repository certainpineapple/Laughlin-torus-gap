import torus.shared.ThermalCoherentBosonRowCanonical
import torus.shared.BosonFiniteCertificateNatPairNormalizedRank
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Actual canonical pair/spectator removals on the finite-support Nat core.
The existing occupation adjoints and polynomial derivative are used directly.
The three-particle vacuum reduction below is proved from homogeneity, before
any original-row matrix or physical periodization is identified. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

def canonicalPairSpectator (p j : ℕ) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (annihilate j).comp (natPairNormalization p • canonicalPairNat p)

/-- The precise unnormalized three-particle source is the true adjoint
multiplier of a_j B_p, with the original pair normalization retained. -/
theorem canonicalPairSpectator_adjoint (p j : ℕ) (f g : Core ℕ ℂ) :
    natOccupationInner ((pairCOMSeed p*MvPolynomial.X j)*f) g =
      natOccupationInner f (canonicalPairSpectator p j g) := by
  rw [pairCOMSeed_eq_canonical_creator,smul_mul_assoc,smul_mul_assoc,mul_assoc,
    ←canonicalPairCreatorNat_eq_mul]
  rw [natOccupationInner_smul_left,natPairNormalization_real,
    canonicalPairCreatorNat_adjoint]
  change natPairNormalization p * natOccupationInner (create j f) (canonicalPairNat p g) = _
  rw [nat_create_adjoint]
  simp only [canonicalPairSpectator,LinearMap.comp_apply,LinearMap.smul_apply,
    map_smul,natOccupationInner_smul_right]

/-- Three actual derivatives leave a true vacuum polynomial on N3. -/
theorem canonicalPairSpectator_homogeneous_zero (p j : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) : (canonicalPairSpectator p j f).IsHomogeneous 0 := by
  simp only [canonicalPairSpectator,LinearMap.comp_apply,LinearMap.smul_apply,
    canonicalPairNat,nat_pair_list_range_sum,LinearMap.sum_apply,
    map_sum,map_smul,LinearMap.comp_apply,LinearMap.smul_apply]
  apply (MvPolynomial.homogeneousSubmodule ℕ ℂ 0).smul_mem
  apply (MvPolynomial.homogeneousSubmodule ℕ ℂ 0).sum_mem
  intro a ha
  apply (MvPolynomial.homogeneousSubmodule ℕ ℂ 0).smul_mem
  change (MvPolynomial.pderiv j (MvPolynomial.pderiv (p-a)
    (MvPolynomial.pderiv a f))).IsHomogeneous 0
  exact ((hN.pderiv (i := a)).pderiv (i := p-a)).pderiv (i := j)

private theorem nat_inner_one (f : Core ℕ ℂ) : natOccupationInner 1 f=f.coeff 0 := by
  change natOccupationInner (MvPolynomial.monomial 0 1) f = _
  rw [natOccupationInner_monomial_left]
  simp [natOccupationWeight,Finsupp.prod]

/-- Exact N3 output, with no occupation multiplicity or normalization omitted. -/
theorem canonicalPairSpectator_vacuum (p j : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) :
    canonicalPairSpectator p j f =
      natOccupationInner (pairCOMSeed p*MvPolynomial.X j) f • (1 : Core ℕ ℂ) := by
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous ℕ).mpr
      (canonicalPairSpectator_homogeneous_zero p j f hN))
  have hi := canonicalPairSpectator_adjoint p j 1 f
  rw [mul_one,nat_inner_one] at hi
  rw [hc,←hi]
  simp only [Algebra.smul_def,mul_one,MvPolynomial.algebraMap_eq]

/-- Any further annihilator really kills the output on N3. -/
theorem canonicalPairSpectator_four_zero (p j i : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) : annihilate i (canonicalPairSpectator p j f)=0 := by
  rw [canonicalPairSpectator_vacuum p j f hN,map_smul]
  change natOccupationInner (pairCOMSeed p*MvPolynomial.X j) f •
    MvPolynomial.pderiv i (1 : Core ℕ ℂ) = 0
  rw [MvPolynomial.pderiv_one,smul_zero]

#print axioms canonicalPairSpectator_adjoint
#print axioms canonicalPairSpectator_homogeneous_zero
#print axioms canonicalPairSpectator_vacuum
#print axioms canonicalPairSpectator_four_zero
end TorusLean.Shared.ThermalCoherentBosonRows
