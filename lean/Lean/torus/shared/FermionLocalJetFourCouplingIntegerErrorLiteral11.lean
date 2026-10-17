import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck11

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck11 :
    integerFourErrorMatrix 11 = TorusLean.FermionM3.errorTable11 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck11]

#print axioms originalIntegerErrorTableCheck11
end TorusLean.Shared.FermionLocalJet.FourCoupling
