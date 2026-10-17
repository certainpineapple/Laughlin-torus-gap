import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 19 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 19 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 19 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 19 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 19 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-4776003085751980204431684375 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 19 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((11078314051077156882088715625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 19 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((69574963478027386990235625 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R5S7 :
    OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (3 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (2 : Fin 10) (3 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R5S7Row0,
    originalYRowSplitD19R5S7Row1,
    originalYRowSplitD19R5S7Row2,
    originalYRowSplitD19R5S7Row3,
    originalYRowSplitD19R5S7Row4,
    originalYRowSplitD19R5S7Row5,
    originalYRowSplitD19R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
