import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck20

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck20 :
    integerFourErrorMatrix 20 = TorusLean.FermionM3.errorTable20 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck20]

#print axioms originalIntegerErrorTableCheck20
end TorusLean.Shared.FermionLocalJet.FourCoupling
