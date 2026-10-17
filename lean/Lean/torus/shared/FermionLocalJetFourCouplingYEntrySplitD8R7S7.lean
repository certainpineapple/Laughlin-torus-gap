import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 8 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((42321625347011687775 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 8 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-7376057539791286839 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 8 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((20829685222835364120795 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 8 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((30544199608275577479675 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 8 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-1243929398768283753645 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 8 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-45894925152507618987405 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 8 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-466714964291950350585 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R7S7 :
    OAI.Laughlin.Certificate.errorRational 8 (3 : Fin 4) (3 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (3 : Fin 4) (3 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R7S7Row0,
    originalYRowSplitD8R7S7Row1,
    originalYRowSplitD8R7S7Row2,
    originalYRowSplitD8R7S7Row3,
    originalYRowSplitD8R7S7Row4,
    originalYRowSplitD8R7S7Row5,
    originalYRowSplitD8R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
