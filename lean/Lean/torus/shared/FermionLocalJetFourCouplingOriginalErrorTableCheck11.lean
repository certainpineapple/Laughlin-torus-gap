import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R1S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R3S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R5S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R7S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R9S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R9S11
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD11R11S11

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck11 :
    OAI.Laughlin.Certificate.errorRational 11 = TorusLean.FermionM3.errorTable11 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD11R1S1
  · exact originalYEntrySplitD11R1S3
  · exact originalYEntrySplitD11R1S5
  · exact originalYEntrySplitD11R1S7
  · exact originalYEntrySplitD11R1S9
  · exact originalYEntrySplitD11R1S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (1 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (0 : Fin 6) (1 : Fin 6) :=
        originalYEntrySplitD11R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD11R3S3
  · exact originalYEntrySplitD11R3S5
  · exact originalYEntrySplitD11R3S7
  · exact originalYEntrySplitD11R3S9
  · exact originalYEntrySplitD11R3S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (2 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (0 : Fin 6) (2 : Fin 6) :=
        originalYEntrySplitD11R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (1 : Fin 6) (2 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (1 : Fin 6) (2 : Fin 6) :=
        originalYEntrySplitD11R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD11R5S5
  · exact originalYEntrySplitD11R5S7
  · exact originalYEntrySplitD11R5S9
  · exact originalYEntrySplitD11R5S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (3 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (0 : Fin 6) (3 : Fin 6) :=
        originalYEntrySplitD11R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (1 : Fin 6) (3 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (1 : Fin 6) (3 : Fin 6) :=
        originalYEntrySplitD11R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (2 : Fin 6) (3 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (2 : Fin 6) (3 : Fin 6) :=
        originalYEntrySplitD11R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD11R7S7
  · exact originalYEntrySplitD11R7S9
  · exact originalYEntrySplitD11R7S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (4 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (0 : Fin 6) (4 : Fin 6) :=
        originalYEntrySplitD11R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (1 : Fin 6) (4 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (1 : Fin 6) (4 : Fin 6) :=
        originalYEntrySplitD11R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (2 : Fin 6) (4 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (2 : Fin 6) (4 : Fin 6) :=
        originalYEntrySplitD11R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (3 : Fin 6) (4 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (3 : Fin 6) (4 : Fin 6) :=
        originalYEntrySplitD11R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD11R9S9
  · exact originalYEntrySplitD11R9S11
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (0 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (0 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD11R1S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (1 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (1 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD11R3S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (2 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (2 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD11R5S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (3 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (3 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD11R7S11
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 11 (4 : Fin 6) (5 : Fin 6) :=
        originalErrorRational_symmetric 11 _ _
      _ = TorusLean.FermionM3.errorTable11 (4 : Fin 6) (5 : Fin 6) :=
        originalYEntrySplitD11R9S11
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD11R11S11

#print axioms originalErrorTableCheck11
end TorusLean.Shared.FermionLocalJet.FourCoupling
