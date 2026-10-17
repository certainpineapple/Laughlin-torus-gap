import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD7R7S7

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck07 :
    OAI.Laughlin.Certificate.errorRational 7 = TorusLean.FermionM3.errorTable07 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD7R1S1
  · exact originalYEntrySplitD7R1S3
  · exact originalYEntrySplitD7R1S5
  · exact originalYEntrySplitD7R1S7
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 7 (0 : Fin 4) (1 : Fin 4) :=
        originalErrorRational_symmetric 7 _ _
      _ = TorusLean.FermionM3.errorTable07 (0 : Fin 4) (1 : Fin 4) :=
        originalYEntrySplitD7R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD7R3S3
  · exact originalYEntrySplitD7R3S5
  · exact originalYEntrySplitD7R3S7
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 7 (0 : Fin 4) (2 : Fin 4) :=
        originalErrorRational_symmetric 7 _ _
      _ = TorusLean.FermionM3.errorTable07 (0 : Fin 4) (2 : Fin 4) :=
        originalYEntrySplitD7R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 7 (1 : Fin 4) (2 : Fin 4) :=
        originalErrorRational_symmetric 7 _ _
      _ = TorusLean.FermionM3.errorTable07 (1 : Fin 4) (2 : Fin 4) :=
        originalYEntrySplitD7R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD7R5S5
  · exact originalYEntrySplitD7R5S7
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 7 (0 : Fin 4) (3 : Fin 4) :=
        originalErrorRational_symmetric 7 _ _
      _ = TorusLean.FermionM3.errorTable07 (0 : Fin 4) (3 : Fin 4) :=
        originalYEntrySplitD7R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 7 (1 : Fin 4) (3 : Fin 4) :=
        originalErrorRational_symmetric 7 _ _
      _ = TorusLean.FermionM3.errorTable07 (1 : Fin 4) (3 : Fin 4) :=
        originalYEntrySplitD7R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 7 (2 : Fin 4) (3 : Fin 4) :=
        originalErrorRational_symmetric 7 _ _
      _ = TorusLean.FermionM3.errorTable07 (2 : Fin 4) (3 : Fin 4) :=
        originalYEntrySplitD7R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD7R7S7

#print axioms originalErrorTableCheck07
end TorusLean.Shared.FermionLocalJet.FourCoupling
