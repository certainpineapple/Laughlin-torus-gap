import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R1S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R3S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R5S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R7S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R9S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R11S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R11S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD13R13S13

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck13 :
    OAI.Laughlin.Certificate.errorRational 13 = TorusLean.FermionM3.errorTable13 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD13R1S1
  · exact originalYEntrySplitD13R1S3
  · exact originalYEntrySplitD13R1S5
  · exact originalYEntrySplitD13R1S7
  · exact originalYEntrySplitD13R1S9
  · exact originalYEntrySplitD13R1S11
  · exact originalYEntrySplitD13R1S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (1 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (0 : Fin 7) (1 : Fin 7) :=
        originalYEntrySplitD13R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD13R3S3
  · exact originalYEntrySplitD13R3S5
  · exact originalYEntrySplitD13R3S7
  · exact originalYEntrySplitD13R3S9
  · exact originalYEntrySplitD13R3S11
  · exact originalYEntrySplitD13R3S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (2 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (0 : Fin 7) (2 : Fin 7) :=
        originalYEntrySplitD13R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (2 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (1 : Fin 7) (2 : Fin 7) :=
        originalYEntrySplitD13R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD13R5S5
  · exact originalYEntrySplitD13R5S7
  · exact originalYEntrySplitD13R5S9
  · exact originalYEntrySplitD13R5S11
  · exact originalYEntrySplitD13R5S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (3 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (0 : Fin 7) (3 : Fin 7) :=
        originalYEntrySplitD13R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (3 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (1 : Fin 7) (3 : Fin 7) :=
        originalYEntrySplitD13R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (2 : Fin 7) (3 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (2 : Fin 7) (3 : Fin 7) :=
        originalYEntrySplitD13R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD13R7S7
  · exact originalYEntrySplitD13R7S9
  · exact originalYEntrySplitD13R7S11
  · exact originalYEntrySplitD13R7S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (4 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (0 : Fin 7) (4 : Fin 7) :=
        originalYEntrySplitD13R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (4 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (1 : Fin 7) (4 : Fin 7) :=
        originalYEntrySplitD13R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (2 : Fin 7) (4 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (2 : Fin 7) (4 : Fin 7) :=
        originalYEntrySplitD13R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (3 : Fin 7) (4 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (3 : Fin 7) (4 : Fin 7) :=
        originalYEntrySplitD13R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD13R9S9
  · exact originalYEntrySplitD13R9S11
  · exact originalYEntrySplitD13R9S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (0 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD13R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (1 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD13R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (2 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (2 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD13R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (3 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (3 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD13R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (4 : Fin 7) (5 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (4 : Fin 7) (5 : Fin 7) :=
        originalYEntrySplitD13R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD13R11S11
  · exact originalYEntrySplitD13R11S13
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (0 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (0 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD13R1S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (1 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD13R3S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (2 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (2 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD13R5S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (3 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (3 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD13R7S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (4 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (4 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD13R9S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 13 (5 : Fin 7) (6 : Fin 7) :=
        originalErrorRational_symmetric 13 _ _
      _ = TorusLean.FermionM3.errorTable13 (5 : Fin 7) (6 : Fin 7) :=
        originalYEntrySplitD13R11S13
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD13R13S13

#print axioms originalErrorTableCheck13
end TorusLean.Shared.FermionLocalJet.FourCoupling
