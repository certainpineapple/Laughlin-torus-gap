import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck23

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck23 :
    integerFourErrorMatrix 23 = TorusLean.FermionM3.errorTable23 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck23]

#print axioms originalIntegerErrorTableCheck23
end TorusLean.Shared.FermionLocalJet.FourCoupling
