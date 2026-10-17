import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD2R1S1

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck02 :
    OAI.Laughlin.Certificate.errorRational 2 = TorusLean.FermionM3.errorTable02 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD2R1S1

#print axioms originalErrorTableCheck02
end TorusLean.Shared.FermionLocalJet.FourCoupling
