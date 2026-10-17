import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck16

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck16 :
    integerFourErrorMatrix 16 = TorusLean.FermionM3.errorTable16 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck16]

#print axioms originalIntegerErrorTableCheck16
end TorusLean.Shared.FermionLocalJet.FourCoupling
