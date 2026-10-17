import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R1S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R1S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R3S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R3S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R5S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R5S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R7S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R7S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R9S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R9S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R11S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R11S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R11S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R13S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R13S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD15R15S15

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck15 :
    OAI.Laughlin.Certificate.errorRational 15 = TorusLean.FermionM3.errorTable15 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD15R1S1
  · exact originalYEntrySplitD15R1S3
  · exact originalYEntrySplitD15R1S5
  · exact originalYEntrySplitD15R1S7
  · exact originalYEntrySplitD15R1S9
  · exact originalYEntrySplitD15R1S11
  · exact originalYEntrySplitD15R1S13
  · exact originalYEntrySplitD15R1S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (1 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (0 : Fin 8) (1 : Fin 8) :=
        originalYEntrySplitD15R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD15R3S3
  · exact originalYEntrySplitD15R3S5
  · exact originalYEntrySplitD15R3S7
  · exact originalYEntrySplitD15R3S9
  · exact originalYEntrySplitD15R3S11
  · exact originalYEntrySplitD15R3S13
  · exact originalYEntrySplitD15R3S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (2 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (0 : Fin 8) (2 : Fin 8) :=
        originalYEntrySplitD15R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (2 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (1 : Fin 8) (2 : Fin 8) :=
        originalYEntrySplitD15R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD15R5S5
  · exact originalYEntrySplitD15R5S7
  · exact originalYEntrySplitD15R5S9
  · exact originalYEntrySplitD15R5S11
  · exact originalYEntrySplitD15R5S13
  · exact originalYEntrySplitD15R5S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (3 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (0 : Fin 8) (3 : Fin 8) :=
        originalYEntrySplitD15R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (3 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (1 : Fin 8) (3 : Fin 8) :=
        originalYEntrySplitD15R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (3 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (2 : Fin 8) (3 : Fin 8) :=
        originalYEntrySplitD15R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD15R7S7
  · exact originalYEntrySplitD15R7S9
  · exact originalYEntrySplitD15R7S11
  · exact originalYEntrySplitD15R7S13
  · exact originalYEntrySplitD15R7S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (4 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (0 : Fin 8) (4 : Fin 8) :=
        originalYEntrySplitD15R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (4 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (1 : Fin 8) (4 : Fin 8) :=
        originalYEntrySplitD15R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (4 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (2 : Fin 8) (4 : Fin 8) :=
        originalYEntrySplitD15R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (3 : Fin 8) (4 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (3 : Fin 8) (4 : Fin 8) :=
        originalYEntrySplitD15R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD15R9S9
  · exact originalYEntrySplitD15R9S11
  · exact originalYEntrySplitD15R9S13
  · exact originalYEntrySplitD15R9S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (0 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD15R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (1 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD15R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (2 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD15R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (3 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (3 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD15R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (4 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (4 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD15R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD15R11S11
  · exact originalYEntrySplitD15R11S13
  · exact originalYEntrySplitD15R11S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (0 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD15R1S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (1 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD15R3S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (2 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD15R5S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (3 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (3 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD15R7S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (4 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (4 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD15R9S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (5 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (5 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD15R11S13
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD15R13S13
  · exact originalYEntrySplitD15R13S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (0 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD15R1S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (1 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD15R3S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (2 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD15R5S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (3 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (3 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD15R7S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (4 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (4 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD15R9S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (5 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (5 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD15R11S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 15 (6 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 15 _ _
      _ = TorusLean.FermionM3.errorTable15 (6 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD15R13S15
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD15R15S15

#print axioms originalErrorTableCheck15
end TorusLean.Shared.FermionLocalJet.FourCoupling
