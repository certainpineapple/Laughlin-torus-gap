import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 12 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((98892247124644386525 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 12 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-2245325603664582225 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 12 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((41407149629605548602475 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 12 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((39246439773802590789075 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 12 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-22282730452806288196725 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 12 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((444439397957774011350525 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 12 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2520027423158122853325 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R7S7 :
    OAI.Laughlin.Certificate.errorRational 12 (3 : Fin 6) (3 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (3 : Fin 6) (3 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R7S7Row0,
    originalYRowSplitD12R7S7Row1,
    originalYRowSplitD12R7S7Row2,
    originalYRowSplitD12R7S7Row3,
    originalYRowSplitD12R7S7Row4,
    originalYRowSplitD12R7S7Row5,
    originalYRowSplitD12R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
