import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck19

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck19 :
    integerFourErrorMatrix 19 = TorusLean.FermionM3.errorTable19 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck19]

#print axioms originalIntegerErrorTableCheck19
end TorusLean.Shared.FermionLocalJet.FourCoupling
