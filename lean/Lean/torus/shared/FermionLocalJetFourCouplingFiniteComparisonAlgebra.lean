import torus.shared.FermionLocalJetFourCouplingFiniteComparisonMiddle

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

theorem four_gram_sandwich_sub_algebra {α : Type*} [Ring α] (R Z K Y : α) :
    ((R*Z*R) * (K-R*Y*R) * (R*Z*R)) =
      R * (Z * (R*K*R - (R*R)*Y*(R*R)) * Z) * R := by
  noncomm_ring

#print axioms four_gram_sandwich_sub_algebra
end TorusLean.Shared.FermionLocalJet.FourCoupling
