import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 19 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 19 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 19 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 19 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 19 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-77222360635010981190097171875 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 19 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((423781798650046947613305928125 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 19 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-5032415809879536169131665625 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R1S7 :
    OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (3 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (0 : Fin 10) (3 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R1S7Row0,
    originalYRowSplitD19R1S7Row1,
    originalYRowSplitD19R1S7Row2,
    originalYRowSplitD19R1S7Row3,
    originalYRowSplitD19R1S7Row4,
    originalYRowSplitD19R1S7Row5,
    originalYRowSplitD19R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
