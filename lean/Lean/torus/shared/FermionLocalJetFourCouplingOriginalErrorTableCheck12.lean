import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD12R11S11

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck12 :
    OAI.Laughlin.Certificate.errorRational 12 = TorusLean.FermionM3.errorTable12 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD12R1S1
  · exact originalYEntrySplitD12R1S3
  · exact originalYEntrySplitD12R1S5
  · exact originalYEntrySplitD12R1S7
  · exact originalYEntrySplitD12R1S9
  · exact originalYEntrySplitD12R1S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (1 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (0 : Fin 6) (1 : Fin 6) :=
        originalYEntrySplitD12R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD12R3S3
  · exact originalYEntrySplitD12R3S5
  · exact originalYEntrySplitD12R3S7
  · exact originalYEntrySplitD12R3S9
  · exact originalYEntrySplitD12R3S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (2 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (0 : Fin 6) (2 : Fin 6) :=
        originalYEntrySplitD12R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (1 : Fin 6) (2 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (1 : Fin 6) (2 : Fin 6) :=
        originalYEntrySplitD12R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD12R5S5
  · exact originalYEntrySplitD12R5S7
  · exact originalYEntrySplitD12R5S9
  · exact originalYEntrySplitD12R5S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (3 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (0 : Fin 6) (3 : Fin 6) :=
        originalYEntrySplitD12R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (1 : Fin 6) (3 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (1 : Fin 6) (3 : Fin 6) :=
        originalYEntrySplitD12R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (2 : Fin 6) (3 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (2 : Fin 6) (3 : Fin 6) :=
        originalYEntrySplitD12R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD12R7S7
  · exact originalYEntrySplitD12R7S9
  · exact originalYEntrySplitD12R7S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (4 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (0 : Fin 6) (4 : Fin 6) :=
        originalYEntrySplitD12R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (1 : Fin 6) (4 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (1 : Fin 6) (4 : Fin 6) :=
        originalYEntrySplitD12R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (2 : Fin 6) (4 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (2 : Fin 6) (4 : Fin 6) :=
        originalYEntrySplitD12R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (3 : Fin 6) (4 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (3 : Fin 6) (4 : Fin 6) :=
        originalYEntrySplitD12R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD12R9S9
  · exact originalYEntrySplitD12R9S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (0 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD12R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (1 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (1 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD12R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (2 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (2 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD12R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (3 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (3 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD12R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 12 (4 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 12 _ _
      _ = TorusLean.FermionM3.errorTable12 (4 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD12R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD12R11S11

#print axioms originalErrorTableCheck12
end TorusLean.Shared.FermionLocalJet.FourCoupling
