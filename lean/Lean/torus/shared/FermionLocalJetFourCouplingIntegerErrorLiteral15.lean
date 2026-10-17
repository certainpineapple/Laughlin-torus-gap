import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck15

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck15 :
    integerFourErrorMatrix 15 = TorusLean.FermionM3.errorTable15 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck15]

#print axioms originalIntegerErrorTableCheck15
end TorusLean.Shared.FermionLocalJet.FourCoupling
