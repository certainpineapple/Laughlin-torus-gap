import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck07

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck07 :
    integerFourErrorMatrix 7 = TorusLean.FermionM3.errorTable07 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck07]

#print axioms originalIntegerErrorTableCheck07
end TorusLean.Shared.FermionLocalJet.FourCoupling
