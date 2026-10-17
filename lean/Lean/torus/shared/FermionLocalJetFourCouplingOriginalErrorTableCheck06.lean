import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD6R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD6R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD6R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD6R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD6R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD6R5S5

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck06 :
    OAI.Laughlin.Certificate.errorRational 6 = TorusLean.FermionM3.errorTable06 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD6R1S1
  · exact originalYEntrySplitD6R1S3
  · exact originalYEntrySplitD6R1S5
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 6 (0 : Fin 3) (1 : Fin 3) :=
        originalErrorRational_symmetric 6 _ _
      _ = TorusLean.FermionM3.errorTable06 (0 : Fin 3) (1 : Fin 3) :=
        originalYEntrySplitD6R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD6R3S3
  · exact originalYEntrySplitD6R3S5
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 6 (0 : Fin 3) (2 : Fin 3) :=
        originalErrorRational_symmetric 6 _ _
      _ = TorusLean.FermionM3.errorTable06 (0 : Fin 3) (2 : Fin 3) :=
        originalYEntrySplitD6R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 6 (1 : Fin 3) (2 : Fin 3) :=
        originalErrorRational_symmetric 6 _ _
      _ = TorusLean.FermionM3.errorTable06 (1 : Fin 3) (2 : Fin 3) :=
        originalYEntrySplitD6R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD6R5S5

#print axioms originalErrorTableCheck06
end TorusLean.Shared.FermionLocalJet.FourCoupling
