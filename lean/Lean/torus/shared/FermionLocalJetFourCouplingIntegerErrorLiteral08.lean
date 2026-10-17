import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck08

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck08 :
    integerFourErrorMatrix 8 = TorusLean.FermionM3.errorTable08 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck08]

#print axioms originalIntegerErrorTableCheck08
end TorusLean.Shared.FermionLocalJet.FourCoupling
