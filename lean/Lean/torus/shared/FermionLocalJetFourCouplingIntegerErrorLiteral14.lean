import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck14

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck14 :
    integerFourErrorMatrix 14 = TorusLean.FermionM3.errorTable14 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck14]

#print axioms originalIntegerErrorTableCheck14
end TorusLean.Shared.FermionLocalJet.FourCoupling
