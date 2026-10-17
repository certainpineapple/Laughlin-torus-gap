import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck18

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck18 :
    integerFourErrorMatrix 18 = TorusLean.FermionM3.errorTable18 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck18]

#print axioms originalIntegerErrorTableCheck18
end TorusLean.Shared.FermionLocalJet.FourCoupling
