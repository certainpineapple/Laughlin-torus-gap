import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck13

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck13 :
    integerFourErrorMatrix 13 = TorusLean.FermionM3.errorTable13 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck13]

#print axioms originalIntegerErrorTableCheck13
end TorusLean.Shared.FermionLocalJet.FourCoupling
