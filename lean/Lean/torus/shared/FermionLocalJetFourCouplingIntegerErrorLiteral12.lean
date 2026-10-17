import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck12

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck12 :
    integerFourErrorMatrix 12 = TorusLean.FermionM3.errorTable12 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck12]

#print axioms originalIntegerErrorTableCheck12
end TorusLean.Shared.FermionLocalJet.FourCoupling
