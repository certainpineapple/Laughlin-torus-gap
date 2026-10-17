import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck06

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck06 :
    integerFourErrorMatrix 6 = TorusLean.FermionM3.errorTable06 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck06]

#print axioms originalIntegerErrorTableCheck06
end TorusLean.Shared.FermionLocalJet.FourCoupling
