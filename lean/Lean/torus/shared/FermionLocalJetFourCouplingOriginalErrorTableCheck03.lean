import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD3R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD3R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD3R3S3

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck03 :
    OAI.Laughlin.Certificate.errorRational 3 = TorusLean.FermionM3.errorTable03 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD3R1S1
  · exact originalYEntrySplitD3R1S3
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 3 (0 : Fin 2) (1 : Fin 2) :=
        originalErrorRational_symmetric 3 _ _
      _ = TorusLean.FermionM3.errorTable03 (0 : Fin 2) (1 : Fin 2) :=
        originalYEntrySplitD3R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD3R3S3

#print axioms originalErrorTableCheck03
end TorusLean.Shared.FermionLocalJet.FourCoupling
