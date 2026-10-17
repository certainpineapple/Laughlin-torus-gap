import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 19 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 19 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 19 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 19 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 19 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((1004370387626648781149709375 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 19 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-883703466040235878926590625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 19 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-9803116259823768748453125 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R7S7 :
    OAI.Laughlin.Certificate.errorRational 19 (3 : Fin 10) (3 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (3 : Fin 10) (3 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R7S7Row0,
    originalYRowSplitD19R7S7Row1,
    originalYRowSplitD19R7S7Row2,
    originalYRowSplitD19R7S7Row3,
    originalYRowSplitD19R7S7Row4,
    originalYRowSplitD19R7S7Row5,
    originalYRowSplitD19R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
