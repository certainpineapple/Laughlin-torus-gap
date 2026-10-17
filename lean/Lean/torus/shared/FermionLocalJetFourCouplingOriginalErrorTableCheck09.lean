import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD9R9S9

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck09 :
    OAI.Laughlin.Certificate.errorRational 9 = TorusLean.FermionM3.errorTable09 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD9R1S1
  · exact originalYEntrySplitD9R1S3
  · exact originalYEntrySplitD9R1S5
  · exact originalYEntrySplitD9R1S7
  · exact originalYEntrySplitD9R1S9
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (0 : Fin 5) (1 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (0 : Fin 5) (1 : Fin 5) :=
        originalYEntrySplitD9R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD9R3S3
  · exact originalYEntrySplitD9R3S5
  · exact originalYEntrySplitD9R3S7
  · exact originalYEntrySplitD9R3S9
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (0 : Fin 5) (2 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (0 : Fin 5) (2 : Fin 5) :=
        originalYEntrySplitD9R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (1 : Fin 5) (2 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (1 : Fin 5) (2 : Fin 5) :=
        originalYEntrySplitD9R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD9R5S5
  · exact originalYEntrySplitD9R5S7
  · exact originalYEntrySplitD9R5S9
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (0 : Fin 5) (3 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (0 : Fin 5) (3 : Fin 5) :=
        originalYEntrySplitD9R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (1 : Fin 5) (3 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (1 : Fin 5) (3 : Fin 5) :=
        originalYEntrySplitD9R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (2 : Fin 5) (3 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (2 : Fin 5) (3 : Fin 5) :=
        originalYEntrySplitD9R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD9R7S7
  · exact originalYEntrySplitD9R7S9
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (0 : Fin 5) (4 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (0 : Fin 5) (4 : Fin 5) :=
        originalYEntrySplitD9R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (1 : Fin 5) (4 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (1 : Fin 5) (4 : Fin 5) :=
        originalYEntrySplitD9R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (2 : Fin 5) (4 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (2 : Fin 5) (4 : Fin 5) :=
        originalYEntrySplitD9R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 9 (3 : Fin 5) (4 : Fin 5) :=
        originalErrorRational_symmetric 9 _ _
      _ = TorusLean.FermionM3.errorTable09 (3 : Fin 5) (4 : Fin 5) :=
        originalYEntrySplitD9R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD9R9S9

#print axioms originalErrorTableCheck09
end TorusLean.Shared.FermionLocalJet.FourCoupling
