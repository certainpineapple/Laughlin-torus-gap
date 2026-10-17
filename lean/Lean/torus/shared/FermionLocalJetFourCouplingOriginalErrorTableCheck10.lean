import torus.shared.FermionLocalJetFourCouplingOriginalYTableSymmetry
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R1S1
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R1S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R1S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R1S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R1S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R3S3
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R3S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R3S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R3S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R5S5
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R5S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R5S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R7S7
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R7S9
import torus.shared.FermionLocalJetFourCouplingYEntrySplitD10R9S9

set_option autoImplicit false
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open YRowSplitCandidate

theorem originalErrorTableCheck10 :
    OAI.Laughlin.Certificate.errorRational 10 = TorusLean.FermionM3.errorTable10 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact originalYEntrySplitD10R1S1
  · exact originalYEntrySplitD10R1S3
  · exact originalYEntrySplitD10R1S5
  · exact originalYEntrySplitD10R1S7
  · exact originalYEntrySplitD10R1S9
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (0 : Fin 5) (1 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (0 : Fin 5) (1 : Fin 5) :=
        originalYEntrySplitD10R1S3
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD10R3S3
  · exact originalYEntrySplitD10R3S5
  · exact originalYEntrySplitD10R3S7
  · exact originalYEntrySplitD10R3S9
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (0 : Fin 5) (2 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (0 : Fin 5) (2 : Fin 5) :=
        originalYEntrySplitD10R1S5
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (1 : Fin 5) (2 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (1 : Fin 5) (2 : Fin 5) :=
        originalYEntrySplitD10R3S5
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD10R5S5
  · exact originalYEntrySplitD10R5S7
  · exact originalYEntrySplitD10R5S9
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (0 : Fin 5) (3 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (0 : Fin 5) (3 : Fin 5) :=
        originalYEntrySplitD10R1S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (1 : Fin 5) (3 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (1 : Fin 5) (3 : Fin 5) :=
        originalYEntrySplitD10R3S7
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (2 : Fin 5) (3 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (2 : Fin 5) (3 : Fin 5) :=
        originalYEntrySplitD10R5S7
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD10R7S7
  · exact originalYEntrySplitD10R7S9
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (0 : Fin 5) (4 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (0 : Fin 5) (4 : Fin 5) :=
        originalYEntrySplitD10R1S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (1 : Fin 5) (4 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (1 : Fin 5) (4 : Fin 5) :=
        originalYEntrySplitD10R3S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (2 : Fin 5) (4 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (2 : Fin 5) (4 : Fin 5) :=
        originalYEntrySplitD10R5S9
      _ = _ := by decide +kernel
  · calc
      _ = OAI.Laughlin.Certificate.errorRational 10 (3 : Fin 5) (4 : Fin 5) :=
        originalErrorRational_symmetric 10 _ _
      _ = TorusLean.FermionM3.errorTable10 (3 : Fin 5) (4 : Fin 5) :=
        originalYEntrySplitD10R7S9
      _ = _ := by decide +kernel
  · exact originalYEntrySplitD10R9S9

#print axioms originalErrorTableCheck10
end TorusLean.Shared.FermionLocalJet.FourCoupling
