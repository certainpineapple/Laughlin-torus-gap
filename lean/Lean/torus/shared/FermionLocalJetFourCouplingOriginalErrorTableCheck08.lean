import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD8R7S7

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck08 :
    OAI.Laughlin.Certificate.errorRational 8 = TorusLean.FermionM3.errorTable08 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD8R1S1
  · exact originalYEntrySplitD8R1S3
  · exact originalYEntrySplitD8R1S5
  · exact originalYEntrySplitD8R1S7
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 8 (0 : Fin 4) (1 : Fin 4) :=
        originalErrorRational_symmetric 8 _ _
      _ = TorusLean.FermionM3.errorTable08 (0 : Fin 4) (1 : Fin 4) :=
        originalYEntrySplitD8R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD8R3S3
  · exact originalYEntrySplitD8R3S5
  · exact originalYEntrySplitD8R3S7
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 8 (0 : Fin 4) (2 : Fin 4) :=
        originalErrorRational_symmetric 8 _ _
      _ = TorusLean.FermionM3.errorTable08 (0 : Fin 4) (2 : Fin 4) :=
        originalYEntrySplitD8R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 8 (1 : Fin 4) (2 : Fin 4) :=
        originalErrorRational_symmetric 8 _ _
      _ = TorusLean.FermionM3.errorTable08 (1 : Fin 4) (2 : Fin 4) :=
        originalYEntrySplitD8R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD8R5S5
  · exact originalYEntrySplitD8R5S7
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 8 (0 : Fin 4) (3 : Fin 4) :=
        originalErrorRational_symmetric 8 _ _
      _ = TorusLean.FermionM3.errorTable08 (0 : Fin 4) (3 : Fin 4) :=
        originalYEntrySplitD8R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 8 (1 : Fin 4) (3 : Fin 4) :=
        originalErrorRational_symmetric 8 _ _
      _ = TorusLean.FermionM3.errorTable08 (1 : Fin 4) (3 : Fin 4) :=
        originalYEntrySplitD8R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 8 (2 : Fin 4) (3 : Fin 4) :=
        originalErrorRational_symmetric 8 _ _
      _ = TorusLean.FermionM3.errorTable08 (2 : Fin 4) (3 : Fin 4) :=
        originalYEntrySplitD8R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD8R7S7

#print axioms originalErrorTableCheck08
end TorusLean.Shared.FermionLocalJet.FourCoupling
