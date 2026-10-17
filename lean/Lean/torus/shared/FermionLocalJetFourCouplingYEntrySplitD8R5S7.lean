import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 8 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-2272256943023826045 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 8 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((265856006788524411 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 8 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-9014338390167069525885 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 8 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-6216612413350207898295 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 8 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((27270331387166645325 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 8 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-26878866420346632296175 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 8 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((16005164678075894895 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R5S7 :
    OAI.Laughlin.Certificate.errorRational 8 (2 : Fin 4) (3 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (2 : Fin 4) (3 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R5S7Row0,
    originalYRowSplitD8R5S7Row1,
    originalYRowSplitD8R5S7Row2,
    originalYRowSplitD8R5S7Row3,
    originalYRowSplitD8R5S7Row4,
    originalYRowSplitD8R5S7Row5,
    originalYRowSplitD8R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
