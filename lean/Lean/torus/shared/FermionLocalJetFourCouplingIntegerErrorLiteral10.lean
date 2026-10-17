import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck10

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck10 :
    integerFourErrorMatrix 10 = TorusLean.FermionM3.errorTable10 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck10]

#print axioms originalIntegerErrorTableCheck10
end TorusLean.Shared.FermionLocalJet.FourCoupling
