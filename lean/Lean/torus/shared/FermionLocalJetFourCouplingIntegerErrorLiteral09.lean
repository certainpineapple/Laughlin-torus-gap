import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck09

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck09 :
    integerFourErrorMatrix 9 = TorusLean.FermionM3.errorTable09 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck09]

#print axioms originalIntegerErrorTableCheck09
end TorusLean.Shared.FermionLocalJet.FourCoupling
