import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck02

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck02 :
    integerFourErrorMatrix 2 = TorusLean.FermionM3.errorTable02 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck02]

#print axioms originalIntegerErrorTableCheck02
end TorusLean.Shared.FermionLocalJet.FourCoupling
