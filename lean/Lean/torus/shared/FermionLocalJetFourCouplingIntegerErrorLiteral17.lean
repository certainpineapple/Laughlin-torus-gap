import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck17

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck17 :
    integerFourErrorMatrix 17 = TorusLean.FermionM3.errorTable17 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck17]

#print axioms originalIntegerErrorTableCheck17
end TorusLean.Shared.FermionLocalJet.FourCoupling
