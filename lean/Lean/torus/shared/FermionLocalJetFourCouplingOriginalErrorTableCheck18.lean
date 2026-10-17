import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R1S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R1S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R1S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R3S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R3S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R3S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R5S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R5S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R5S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R7S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R7S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R7S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R9S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R9S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R9S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R11S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R11S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R11S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R11S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R13S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R13S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R13S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R15S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R15S17
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD18R17S17

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck18 :
    OAI.Laughlin.Certificate.errorRational 18 = TorusLean.FermionM3.errorTable18 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD18R1S1
  · exact originalYEntrySplitD18R1S3
  · exact originalYEntrySplitD18R1S5
  · exact originalYEntrySplitD18R1S7
  · exact originalYEntrySplitD18R1S9
  · exact originalYEntrySplitD18R1S11
  · exact originalYEntrySplitD18R1S13
  · exact originalYEntrySplitD18R1S15
  · exact originalYEntrySplitD18R1S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (1 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (0 : Fin 9) (1 : Fin 9) :=
        originalYEntrySplitD18R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD18R3S3
  · exact originalYEntrySplitD18R3S5
  · exact originalYEntrySplitD18R3S7
  · exact originalYEntrySplitD18R3S9
  · exact originalYEntrySplitD18R3S11
  · exact originalYEntrySplitD18R3S13
  · exact originalYEntrySplitD18R3S15
  · exact originalYEntrySplitD18R3S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (2 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (0 : Fin 9) (2 : Fin 9) :=
        originalYEntrySplitD18R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (2 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (1 : Fin 9) (2 : Fin 9) :=
        originalYEntrySplitD18R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD18R5S5
  · exact originalYEntrySplitD18R5S7
  · exact originalYEntrySplitD18R5S9
  · exact originalYEntrySplitD18R5S11
  · exact originalYEntrySplitD18R5S13
  · exact originalYEntrySplitD18R5S15
  · exact originalYEntrySplitD18R5S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (3 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (0 : Fin 9) (3 : Fin 9) :=
        originalYEntrySplitD18R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (3 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (1 : Fin 9) (3 : Fin 9) :=
        originalYEntrySplitD18R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (3 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (2 : Fin 9) (3 : Fin 9) :=
        originalYEntrySplitD18R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD18R7S7
  · exact originalYEntrySplitD18R7S9
  · exact originalYEntrySplitD18R7S11
  · exact originalYEntrySplitD18R7S13
  · exact originalYEntrySplitD18R7S15
  · exact originalYEntrySplitD18R7S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (4 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (0 : Fin 9) (4 : Fin 9) :=
        originalYEntrySplitD18R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (4 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (1 : Fin 9) (4 : Fin 9) :=
        originalYEntrySplitD18R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (4 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (2 : Fin 9) (4 : Fin 9) :=
        originalYEntrySplitD18R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (3 : Fin 9) (4 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (3 : Fin 9) (4 : Fin 9) :=
        originalYEntrySplitD18R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD18R9S9
  · exact originalYEntrySplitD18R9S11
  · exact originalYEntrySplitD18R9S13
  · exact originalYEntrySplitD18R9S15
  · exact originalYEntrySplitD18R9S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (0 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD18R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (1 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD18R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (2 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD18R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (3 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (3 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD18R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (4 : Fin 9) (5 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (4 : Fin 9) (5 : Fin 9) :=
        originalYEntrySplitD18R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD18R11S11
  · exact originalYEntrySplitD18R11S13
  · exact originalYEntrySplitD18R11S15
  · exact originalYEntrySplitD18R11S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (0 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD18R1S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (1 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD18R3S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (2 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD18R5S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (3 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (3 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD18R7S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (4 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (4 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD18R9S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (5 : Fin 9) (6 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (5 : Fin 9) (6 : Fin 9) :=
        originalYEntrySplitD18R11S13
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD18R13S13
  · exact originalYEntrySplitD18R13S15
  · exact originalYEntrySplitD18R13S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (0 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD18R1S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (1 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD18R3S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (2 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD18R5S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (3 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (3 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD18R7S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (4 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (4 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD18R9S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (5 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (5 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD18R11S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (6 : Fin 9) (7 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (6 : Fin 9) (7 : Fin 9) :=
        originalYEntrySplitD18R13S15
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD18R15S15
  · exact originalYEntrySplitD18R15S17
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (0 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD18R1S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (1 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD18R3S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (2 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD18R5S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (3 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (3 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD18R7S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (4 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (4 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD18R9S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (5 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (5 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD18R11S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (6 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (6 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD18R13S17
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 18 (7 : Fin 9) (8 : Fin 9) :=
        originalErrorRational_symmetric 18 _ _
      _ = TorusLean.FermionM3.errorTable18 (7 : Fin 9) (8 : Fin 9) :=
        originalYEntrySplitD18R15S17
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD18R17S17

#print axioms originalErrorTableCheck18
end TorusLean.Shared.FermionLocalJet.FourCoupling
