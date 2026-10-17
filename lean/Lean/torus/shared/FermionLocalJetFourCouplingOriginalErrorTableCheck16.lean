import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R1S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R1S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R3S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R3S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R5S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R5S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R7S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R7S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R9S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R9S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R11S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R11S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R11S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R13S13
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R13S15
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD16R15S15

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck16 :
    OAI.Laughlin.Certificate.errorRational 16 = TorusLean.FermionM3.errorTable16 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD16R1S1
  · exact originalYEntrySplitD16R1S3
  · exact originalYEntrySplitD16R1S5
  · exact originalYEntrySplitD16R1S7
  · exact originalYEntrySplitD16R1S9
  · exact originalYEntrySplitD16R1S11
  · exact originalYEntrySplitD16R1S13
  · exact originalYEntrySplitD16R1S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (1 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (0 : Fin 8) (1 : Fin 8) :=
        originalYEntrySplitD16R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD16R3S3
  · exact originalYEntrySplitD16R3S5
  · exact originalYEntrySplitD16R3S7
  · exact originalYEntrySplitD16R3S9
  · exact originalYEntrySplitD16R3S11
  · exact originalYEntrySplitD16R3S13
  · exact originalYEntrySplitD16R3S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (2 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (0 : Fin 8) (2 : Fin 8) :=
        originalYEntrySplitD16R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (2 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (1 : Fin 8) (2 : Fin 8) :=
        originalYEntrySplitD16R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD16R5S5
  · exact originalYEntrySplitD16R5S7
  · exact originalYEntrySplitD16R5S9
  · exact originalYEntrySplitD16R5S11
  · exact originalYEntrySplitD16R5S13
  · exact originalYEntrySplitD16R5S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (3 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (0 : Fin 8) (3 : Fin 8) :=
        originalYEntrySplitD16R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (3 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (1 : Fin 8) (3 : Fin 8) :=
        originalYEntrySplitD16R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (3 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (2 : Fin 8) (3 : Fin 8) :=
        originalYEntrySplitD16R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD16R7S7
  · exact originalYEntrySplitD16R7S9
  · exact originalYEntrySplitD16R7S11
  · exact originalYEntrySplitD16R7S13
  · exact originalYEntrySplitD16R7S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (4 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (0 : Fin 8) (4 : Fin 8) :=
        originalYEntrySplitD16R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (4 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (1 : Fin 8) (4 : Fin 8) :=
        originalYEntrySplitD16R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (4 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (2 : Fin 8) (4 : Fin 8) :=
        originalYEntrySplitD16R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (3 : Fin 8) (4 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (3 : Fin 8) (4 : Fin 8) :=
        originalYEntrySplitD16R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD16R9S9
  · exact originalYEntrySplitD16R9S11
  · exact originalYEntrySplitD16R9S13
  · exact originalYEntrySplitD16R9S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (0 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD16R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (1 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD16R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (2 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD16R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (3 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (3 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD16R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (4 : Fin 8) (5 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (4 : Fin 8) (5 : Fin 8) :=
        originalYEntrySplitD16R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD16R11S11
  · exact originalYEntrySplitD16R11S13
  · exact originalYEntrySplitD16R11S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (0 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD16R1S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (1 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD16R3S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (2 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD16R5S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (3 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (3 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD16R7S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (4 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (4 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD16R9S13
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (5 : Fin 8) (6 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (5 : Fin 8) (6 : Fin 8) :=
        originalYEntrySplitD16R11S13
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD16R13S13
  · exact originalYEntrySplitD16R13S15
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (0 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD16R1S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (1 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD16R3S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (2 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD16R5S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (3 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (3 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD16R7S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (4 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (4 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD16R9S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (5 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (5 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD16R11S15
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 16 (6 : Fin 8) (7 : Fin 8) :=
        originalErrorRational_symmetric 16 _ _
      _ = TorusLean.FermionM3.errorTable16 (6 : Fin 8) (7 : Fin 8) :=
        originalYEntrySplitD16R13S15
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD16R15S15

#print axioms originalErrorTableCheck16
end TorusLean.Shared.FermionLocalJet.FourCoupling
