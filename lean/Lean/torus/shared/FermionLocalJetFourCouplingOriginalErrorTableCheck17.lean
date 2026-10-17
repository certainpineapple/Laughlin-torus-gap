import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R1S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R1S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R1S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R3S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R3S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R3S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R5S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R5S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R5S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R7S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R7S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R7S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R9S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R9S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R9S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R11S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R11S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R11S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R11S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R13S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R13S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R13S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R15S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R15S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD17R17S17

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck17 :
    OAI.Laughlin.Certificate.errorRational 17 = TorusLean.FermionM3.errorTable17 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD17R1S1
  · exact originalYEntrySplitD17R1S3
  · exact originalYEntrySplitD17R1S5
  · exact originalYEntrySplitD17R1S7
  · exact originalYEntrySplitD17R1S9
  · exact originalYEntrySplitD17R1S11
  · exact originalYEntrySplitD17R1S13
  · exact originalYEntrySplitD17R1S15
  · exact originalYEntrySplitD17R1S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (1 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (0 : Fin 9) (1 : Fin 9) :=
        originalYEntrySplitD17R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD17R3S3
  · exact originalYEntrySplitD17R3S5
  · exact originalYEntrySplitD17R3S7
  · exact originalYEntrySplitD17R3S9
  · exact originalYEntrySplitD17R3S11
  · exact originalYEntrySplitD17R3S13
  · exact originalYEntrySplitD17R3S15
  · exact originalYEntrySplitD17R3S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (2 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (0 : Fin 9) (2 : Fin 9) :=
        originalYEntrySplitD17R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (2 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (1 : Fin 9) (2 : Fin 9) :=
        originalYEntrySplitD17R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD17R5S5
  · exact originalYEntrySplitD17R5S7
  · exact originalYEntrySplitD17R5S9
  · exact originalYEntrySplitD17R5S11
  · exact originalYEntrySplitD17R5S13
  · exact originalYEntrySplitD17R5S15
  · exact originalYEntrySplitD17R5S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (3 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (0 : Fin 9) (3 : Fin 9) :=
        originalYEntrySplitD17R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (3 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (1 : Fin 9) (3 : Fin 9) :=
        originalYEntrySplitD17R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (3 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (2 : Fin 9) (3 : Fin 9) :=
        originalYEntrySplitD17R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD17R7S7
  · exact originalYEntrySplitD17R7S9
  · exact originalYEntrySplitD17R7S11
  · exact originalYEntrySplitD17R7S13
  · exact originalYEntrySplitD17R7S15
  · exact originalYEntrySplitD17R7S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (4 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (0 : Fin 9) (4 : Fin 9) :=
        originalYEntrySplitD17R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (4 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (1 : Fin 9) (4 : Fin 9) :=
        originalYEntrySplitD17R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (4 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (2 : Fin 9) (4 : Fin 9) :=
        originalYEntrySplitD17R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (3 : Fin 9) (4 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (3 : Fin 9) (4 : Fin 9) :=
        originalYEntrySplitD17R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD17R9S9
  · exact originalYEntrySplitD17R9S11
  · exact originalYEntrySplitD17R9S13
  · exact originalYEntrySplitD17R9S15
  · exact originalYEntrySplitD17R9S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (0 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD17R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (1 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD17R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (2 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD17R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (3 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (3 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD17R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (4 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (4 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD17R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD17R11S11
  · exact originalYEntrySplitD17R11S13
  · exact originalYEntrySplitD17R11S15
  · exact originalYEntrySplitD17R11S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (0 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD17R1S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (1 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD17R3S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (2 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD17R5S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (3 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (3 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD17R7S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (4 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (4 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD17R9S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (5 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (5 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD17R11S13
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD17R13S13
  · exact originalYEntrySplitD17R13S15
  · exact originalYEntrySplitD17R13S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (0 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD17R1S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (1 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD17R3S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (2 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD17R5S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (3 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (3 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD17R7S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (4 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (4 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD17R9S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (5 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (5 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD17R11S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (6 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (6 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD17R13S15
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD17R15S15
  · exact originalYEntrySplitD17R15S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (0 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD17R1S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (1 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD17R3S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (2 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD17R5S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (3 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (3 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD17R7S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (4 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (4 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD17R9S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (5 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (5 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD17R11S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (6 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (6 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD17R13S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 17 (7 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 17 _ _
      _ = TorusLean.FermionM3.errorTable17 (7 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD17R15S17
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD17R17S17

#print axioms originalErrorTableCheck17
end TorusLean.Shared.FermionLocalJet.FourCoupling
