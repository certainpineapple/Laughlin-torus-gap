import torus.shared.FermionLocalJetFourCouplingIntegerErrorUBridge
import torus.shared.FermionLocalJetFourCouplingOriginalErrorTableCheck03

set_option autoImplicit false
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalIntegerErrorTableCheck03 :
    integerFourErrorMatrix 3 = TorusLean.FermionM3.errorTable03 := by
  rw [integerFourErrorMatrix_eq_originalY,originalErrorTableCheck03]

#print axioms originalIntegerErrorTableCheck03
end TorusLean.Shared.FermionLocalJet.FourCoupling
