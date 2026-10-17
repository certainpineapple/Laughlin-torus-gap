import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD1R1S1

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck01 :
    OAI.Laughlin.Certificate.errorRational 1 = TorusLean.FermionM3.errorTable01 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD1R1S1

#print axioms originalErrorTableCheck01
end TorusLean.Shared.FermionLocalJet.FourCoupling
