import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R1S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R3S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R3S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R3S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R3S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R5S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R5S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R5S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R5S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R7S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R7S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R7S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R7S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R9S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R9S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R9S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R9S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R11S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R11S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R11S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R11S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R11S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R13S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R13S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R13S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R13S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R15S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R15S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R15S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R17S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R17S19
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD20R19S19

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck20 :
    OAI.Laughlin.Certificate.errorRational 20 = TorusLean.FermionM3.errorTable20 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD20R1S1
  · exact originalYEntrySplitD20R1S3
  · exact originalYEntrySplitD20R1S5
  · exact originalYEntrySplitD20R1S7
  · exact originalYEntrySplitD20R1S9
  · exact originalYEntrySplitD20R1S11
  · exact originalYEntrySplitD20R1S13
  · exact originalYEntrySplitD20R1S15
  · exact originalYEntrySplitD20R1S17
  · exact originalYEntrySplitD20R1S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (1 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (0 : Fin 10) (1 : Fin 10) :=
        originalYEntrySplitD20R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD20R3S3
  · exact originalYEntrySplitD20R3S5
  · exact originalYEntrySplitD20R3S7
  · exact originalYEntrySplitD20R3S9
  · exact originalYEntrySplitD20R3S11
  · exact originalYEntrySplitD20R3S13
  · exact originalYEntrySplitD20R3S15
  · exact originalYEntrySplitD20R3S17
  · exact originalYEntrySplitD20R3S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (2 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (0 : Fin 10) (2 : Fin 10) :=
        originalYEntrySplitD20R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (2 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (1 : Fin 10) (2 : Fin 10) :=
        originalYEntrySplitD20R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD20R5S5
  · exact originalYEntrySplitD20R5S7
  · exact originalYEntrySplitD20R5S9
  · exact originalYEntrySplitD20R5S11
  · exact originalYEntrySplitD20R5S13
  · exact originalYEntrySplitD20R5S15
  · exact originalYEntrySplitD20R5S17
  · exact originalYEntrySplitD20R5S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (3 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (0 : Fin 10) (3 : Fin 10) :=
        originalYEntrySplitD20R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (3 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (1 : Fin 10) (3 : Fin 10) :=
        originalYEntrySplitD20R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (2 : Fin 10) (3 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (2 : Fin 10) (3 : Fin 10) :=
        originalYEntrySplitD20R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD20R7S7
  · exact originalYEntrySplitD20R7S9
  · exact originalYEntrySplitD20R7S11
  · exact originalYEntrySplitD20R7S13
  · exact originalYEntrySplitD20R7S15
  · exact originalYEntrySplitD20R7S17
  · exact originalYEntrySplitD20R7S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (4 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (0 : Fin 10) (4 : Fin 10) :=
        originalYEntrySplitD20R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (4 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (1 : Fin 10) (4 : Fin 10) :=
        originalYEntrySplitD20R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (2 : Fin 10) (4 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (2 : Fin 10) (4 : Fin 10) :=
        originalYEntrySplitD20R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (3 : Fin 10) (4 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (3 : Fin 10) (4 : Fin 10) :=
        originalYEntrySplitD20R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD20R9S9
  · exact originalYEntrySplitD20R9S11
  · exact originalYEntrySplitD20R9S13
  · exact originalYEntrySplitD20R9S15
  · exact originalYEntrySplitD20R9S17
  · exact originalYEntrySplitD20R9S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (0 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD20R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (1 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD20R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (2 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (2 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD20R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (3 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (3 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD20R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (4 : Fin 10) (5 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (4 : Fin 10) (5 : Fin 10) :=
        originalYEntrySplitD20R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD20R11S11
  · exact originalYEntrySplitD20R11S13
  · exact originalYEntrySplitD20R11S15
  · exact originalYEntrySplitD20R11S17
  · exact originalYEntrySplitD20R11S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (0 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD20R1S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (1 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD20R3S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (2 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (2 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD20R5S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (3 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (3 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD20R7S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (4 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (4 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD20R9S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (5 : Fin 10) (6 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (5 : Fin 10) (6 : Fin 10) :=
        originalYEntrySplitD20R11S13
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD20R13S13
  · exact originalYEntrySplitD20R13S15
  · exact originalYEntrySplitD20R13S17
  · exact originalYEntrySplitD20R13S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (0 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD20R1S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (1 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD20R3S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (2 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (2 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD20R5S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (3 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (3 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD20R7S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (4 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (4 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD20R9S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (5 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (5 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD20R11S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (6 : Fin 10) (7 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (6 : Fin 10) (7 : Fin 10) :=
        originalYEntrySplitD20R13S15
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD20R15S15
  · exact originalYEntrySplitD20R15S17
  · exact originalYEntrySplitD20R15S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (0 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD20R1S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (1 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD20R3S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (2 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (2 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD20R5S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (3 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (3 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD20R7S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (4 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (4 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD20R9S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (5 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (5 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD20R11S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (6 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (6 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD20R13S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (7 : Fin 10) (8 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (7 : Fin 10) (8 : Fin 10) :=
        originalYEntrySplitD20R15S17
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD20R17S17
  · exact originalYEntrySplitD20R17S19
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (0 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD20R1S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (1 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD20R3S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (2 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (2 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD20R5S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (3 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (3 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD20R7S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (4 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (4 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD20R9S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (5 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (5 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD20R11S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (6 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (6 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD20R13S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (7 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (7 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD20R15S19
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 20 (8 : Fin 10) (9 : Fin 10) :=
        originalErrorRational_symmetric 20 _ _
      _ = TorusLean.FermionM3.errorTable20 (8 : Fin 10) (9 : Fin 10) :=
        originalYEntrySplitD20R17S19
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD20R19S19

#print axioms originalErrorTableCheck20
end TorusLean.Shared.FermionLocalJet.FourCoupling
