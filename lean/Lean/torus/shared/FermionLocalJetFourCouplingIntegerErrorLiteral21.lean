import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck21

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck21 :
    integerFourErrorMatrix 21 = TorusLean.FermionM3.errorTable21 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck21]

#print axioms originalIntegerErrorTableCheck21
end TorusLean.Shared.FermionLocalJet.FourCoupling
