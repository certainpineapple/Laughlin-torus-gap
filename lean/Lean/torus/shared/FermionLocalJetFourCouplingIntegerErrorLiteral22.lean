import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck22

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck22 :
    integerFourErrorMatrix 22 = TorusLean.FermionM3.errorTable22 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck22]

#print axioms originalIntegerErrorTableCheck22
end TorusLean.Shared.FermionLocalJet.FourCoupling
