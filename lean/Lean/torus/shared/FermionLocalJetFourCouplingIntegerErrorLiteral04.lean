import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck04

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck04 :
    integerFourErrorMatrix 4 = TorusLean.FermionM3.errorTable04 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck04]

#print axioms originalIntegerErrorTableCheck04
end TorusLean.Shared.FermionLocalJet.FourCoupling
