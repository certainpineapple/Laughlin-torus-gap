import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD5R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD5R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD5R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD5R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD5R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD5R5S5

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck05 :
    OAI.Laughlin.Certificate.errorRational 5 = TorusLean.FermionM3.errorTable05 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD5R1S1
  · exact originalYEntrySplitD5R1S3
  · exact originalYEntrySplitD5R1S5
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 5 (0 : Fin 3) (1 : Fin 3) :=
        originalErrorRational_symmetric 5 _ _
      _ = TorusLean.FermionM3.errorTable05 (0 : Fin 3) (1 : Fin 3) :=
        originalYEntrySplitD5R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD5R3S3
  · exact originalYEntrySplitD5R3S5
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 5 (0 : Fin 3) (2 : Fin 3) :=
        originalErrorRational_symmetric 5 _ _
      _ = TorusLean.FermionM3.errorTable05 (0 : Fin 3) (2 : Fin 3) :=
        originalYEntrySplitD5R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 5 (1 : Fin 3) (2 : Fin 3) :=
        originalErrorRational_symmetric 5 _ _
      _ = TorusLean.FermionM3.errorTable05 (1 : Fin 3) (2 : Fin 3) :=
        originalYEntrySplitD5R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD5R5S5

#print axioms originalErrorTableCheck05
end TorusLean.Shared.FermionLocalJet.FourCoupling
