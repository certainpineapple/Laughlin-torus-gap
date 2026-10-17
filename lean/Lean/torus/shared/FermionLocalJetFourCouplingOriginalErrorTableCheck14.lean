import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R1S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R3S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R5S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R7S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R9S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R11S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R11S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD14R13S13

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck14 :
    OAI.Laughlin.Certificate.errorRational 14 = TorusLean.FermionM3.errorTable14 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD14R1S1
  · exact originalYEntrySplitD14R1S3
  · exact originalYEntrySplitD14R1S5
  · exact originalYEntrySplitD14R1S7
  · exact originalYEntrySplitD14R1S9
  · exact originalYEntrySplitD14R1S11
  · exact originalYEntrySplitD14R1S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (1 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (0 : Fin 7) (1 : Fin 7) :=
        originalYEntrySplitD14R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD14R3S3
  · exact originalYEntrySplitD14R3S5
  · exact originalYEntrySplitD14R3S7
  · exact originalYEntrySplitD14R3S9
  · exact originalYEntrySplitD14R3S11
  · exact originalYEntrySplitD14R3S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (2 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (0 : Fin 7) (2 : Fin 7) :=
        originalYEntrySplitD14R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (2 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (1 : Fin 7) (2 : Fin 7) :=
        originalYEntrySplitD14R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD14R5S5
  · exact originalYEntrySplitD14R5S7
  · exact originalYEntrySplitD14R5S9
  · exact originalYEntrySplitD14R5S11
  · exact originalYEntrySplitD14R5S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (3 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (0 : Fin 7) (3 : Fin 7) :=
        originalYEntrySplitD14R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (3 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (1 : Fin 7) (3 : Fin 7) :=
        originalYEntrySplitD14R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (2 : Fin 7) (3 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (2 : Fin 7) (3 : Fin 7) :=
        originalYEntrySplitD14R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD14R7S7
  · exact originalYEntrySplitD14R7S9
  · exact originalYEntrySplitD14R7S11
  · exact originalYEntrySplitD14R7S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (4 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (0 : Fin 7) (4 : Fin 7) :=
        originalYEntrySplitD14R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (4 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (1 : Fin 7) (4 : Fin 7) :=
        originalYEntrySplitD14R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (2 : Fin 7) (4 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (2 : Fin 7) (4 : Fin 7) :=
        originalYEntrySplitD14R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (3 : Fin 7) (4 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (3 : Fin 7) (4 : Fin 7) :=
        originalYEntrySplitD14R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD14R9S9
  · exact originalYEntrySplitD14R9S11
  · exact originalYEntrySplitD14R9S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (0 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD14R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (1 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD14R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (2 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (2 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD14R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (3 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (3 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD14R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (4 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (4 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD14R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD14R11S11
  · exact originalYEntrySplitD14R11S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (0 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD14R1S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (1 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD14R3S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (2 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (2 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD14R5S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (3 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (3 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD14R7S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (4 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (4 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD14R9S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 14 (5 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 14 _ _
      _ = TorusLean.FermionM3.errorTable14 (5 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD14R11S13
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD14R13S13

#print axioms originalErrorTableCheck14
end TorusLean.Shared.FermionLocalJet.FourCoupling
