import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 19 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 19 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 19 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 19 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 19 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((5834825856416597295827432235375 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 19 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-20671361028067583527131128315625 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 19 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((21086884731337399212664300875 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R1S1 :
    OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (0 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (0 : Fin 10) (0 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R1S1Row0,
    originalYRowSplitD19R1S1Row1,
    originalYRowSplitD19R1S1Row2,
    originalYRowSplitD19R1S1Row3,
    originalYRowSplitD19R1S1Row4,
    originalYRowSplitD19R1S1Row5,
    originalYRowSplitD19R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
