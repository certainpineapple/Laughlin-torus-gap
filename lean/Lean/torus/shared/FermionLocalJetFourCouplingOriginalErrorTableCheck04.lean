import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD4R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD4R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD4R3S3

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck04 :
    OAI.Laughlin.Certificate.errorRational 4 = TorusLean.FermionM3.errorTable04 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD4R1S1
  · exact originalYEntrySplitD4R1S3
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 4 (0 : Fin 2) (1 : Fin 2) :=
        originalErrorRational_symmetric 4 _ _
      _ = TorusLean.FermionM3.errorTable04 (0 : Fin 2) (1 : Fin 2) :=
        originalYEntrySplitD4R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD4R3S3

#print axioms originalErrorTableCheck04
end TorusLean.Shared.FermionLocalJet.FourCoupling
