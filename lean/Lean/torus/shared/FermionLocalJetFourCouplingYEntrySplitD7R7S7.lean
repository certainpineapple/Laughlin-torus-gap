import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 7 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((23600622017985557895 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 7 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((48841871261567267859 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 7 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-21796542666481881573405 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 7 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((23162047839316984778355 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 7 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((66973353174085436915265 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 7 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-501028086213336269895615 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 7 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-272062846972941081435 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R7S7 :
    OAI.Laughlin.Certificate.errorRational 7 (3 : Fin 4) (3 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (3 : Fin 4) (3 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R7S7Row0,
    originalYRowSplitD7R7S7Row1,
    originalYRowSplitD7R7S7Row2,
    originalYRowSplitD7R7S7Row3,
    originalYRowSplitD7R7S7Row4,
    originalYRowSplitD7R7S7Row5,
    originalYRowSplitD7R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
