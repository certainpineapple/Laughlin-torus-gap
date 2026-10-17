import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck01

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck01 :
    integerFourErrorMatrix 1 = TorusLean.FermionM3.errorTable01 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck01]

#print axioms originalIntegerErrorTableCheck01
end TorusLean.Shared.FermionLocalJet.FourCoupling
