import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck05

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck05 :
    integerFourErrorMatrix 5 = TorusLean.FermionM3.errorTable05 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck05]

#print axioms originalIntegerErrorTableCheck05
end TorusLean.Shared.FermionLocalJet.FourCoupling
