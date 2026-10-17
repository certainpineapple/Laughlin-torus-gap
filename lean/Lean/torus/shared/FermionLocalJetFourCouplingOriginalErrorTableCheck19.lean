import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R1S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R3S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R3S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R3S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R3S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R5S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R5S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R5S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R5S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R7S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R7S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R7S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R7S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R9S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R9S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R9S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R9S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R11S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R11S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R11S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R11S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R11S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R13S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R13S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R13S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R13S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R15S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R15S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R15S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R17S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R17S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD19R19S19

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck19 :
    OAI.Laughlin.Certificate.errorRational 19 = TorusLean.FermionM3.errorTable19 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD19R1S1
  · exact originalYEntrySplitD19R1S3
  · exact originalYEntrySplitD19R1S5
  · exact originalYEntrySplitD19R1S7
  · exact originalYEntrySplitD19R1S9
  · exact originalYEntrySplitD19R1S11
  · exact originalYEntrySplitD19R1S13
  · exact originalYEntrySplitD19R1S15
  · exact originalYEntrySplitD19R1S17
  · exact originalYEntrySplitD19R1S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (1 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (0 : Fin 10) (1 : Fin 10) :=
        originalYEntrySplitD19R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD19R3S3
  · exact originalYEntrySplitD19R3S5
  · exact originalYEntrySplitD19R3S7
  · exact originalYEntrySplitD19R3S9
  · exact originalYEntrySplitD19R3S11
  · exact originalYEntrySplitD19R3S13
  · exact originalYEntrySplitD19R3S15
  · exact originalYEntrySplitD19R3S17
  · exact originalYEntrySplitD19R3S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (2 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (0 : Fin 10) (2 : Fin 10) :=
        originalYEntrySplitD19R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (2 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (1 : Fin 10) (2 : Fin 10) :=
        originalYEntrySplitD19R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD19R5S5
  · exact originalYEntrySplitD19R5S7
  · exact originalYEntrySplitD19R5S9
  · exact originalYEntrySplitD19R5S11
  · exact originalYEntrySplitD19R5S13
  · exact originalYEntrySplitD19R5S15
  · exact originalYEntrySplitD19R5S17
  · exact originalYEntrySplitD19R5S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (3 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (0 : Fin 10) (3 : Fin 10) :=
        originalYEntrySplitD19R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (3 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (1 : Fin 10) (3 : Fin 10) :=
        originalYEntrySplitD19R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (3 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (2 : Fin 10) (3 : Fin 10) :=
        originalYEntrySplitD19R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD19R7S7
  · exact originalYEntrySplitD19R7S9
  · exact originalYEntrySplitD19R7S11
  · exact originalYEntrySplitD19R7S13
  · exact originalYEntrySplitD19R7S15
  · exact originalYEntrySplitD19R7S17
  · exact originalYEntrySplitD19R7S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (4 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (0 : Fin 10) (4 : Fin 10) :=
        originalYEntrySplitD19R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (4 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (1 : Fin 10) (4 : Fin 10) :=
        originalYEntrySplitD19R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (4 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (2 : Fin 10) (4 : Fin 10) :=
        originalYEntrySplitD19R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (3 : Fin 10) (4 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (3 : Fin 10) (4 : Fin 10) :=
        originalYEntrySplitD19R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD19R9S9
  · exact originalYEntrySplitD19R9S11
  · exact originalYEntrySplitD19R9S13
  · exact originalYEntrySplitD19R9S15
  · exact originalYEntrySplitD19R9S17
  · exact originalYEntrySplitD19R9S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (0 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD19R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (1 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD19R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (2 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD19R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (3 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (3 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD19R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (4 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (4 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD19R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD19R11S11
  · exact originalYEntrySplitD19R11S13
  · exact originalYEntrySplitD19R11S15
  · exact originalYEntrySplitD19R11S17
  · exact originalYEntrySplitD19R11S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (0 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD19R1S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (1 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD19R3S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (2 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD19R5S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (3 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (3 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD19R7S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (4 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (4 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD19R9S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (5 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (5 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD19R11S13
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD19R13S13
  · exact originalYEntrySplitD19R13S15
  · exact originalYEntrySplitD19R13S17
  · exact originalYEntrySplitD19R13S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (0 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD19R1S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (1 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD19R3S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (2 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD19R5S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (3 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (3 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD19R7S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (4 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (4 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD19R9S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (5 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (5 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD19R11S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (6 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (6 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD19R13S15
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD19R15S15
  · exact originalYEntrySplitD19R15S17
  · exact originalYEntrySplitD19R15S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (0 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD19R1S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (1 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD19R3S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (2 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD19R5S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (3 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (3 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD19R7S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (4 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (4 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD19R9S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (5 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (5 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD19R11S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (6 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (6 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD19R13S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (7 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (7 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD19R15S17
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD19R17S17
  · exact originalYEntrySplitD19R17S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (0 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD19R1S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (1 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD19R3S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (2 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD19R5S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (3 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (3 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD19R7S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (4 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (4 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD19R9S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (5 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (5 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD19R11S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (6 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (6 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD19R13S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (7 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (7 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD19R15S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 19 (8 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 19 _ _
      _ = TorusLean.FermionM3.errorTable19 (8 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD19R17S19
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD19R19S19

#print axioms originalErrorTableCheck19
end TorusLean.Shared.FermionLocalJet.FourCoupling
