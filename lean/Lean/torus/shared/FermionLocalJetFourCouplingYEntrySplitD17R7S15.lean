import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R7S15Row0 :
    OAI.Laughlin.Certificate.yRow 17 7 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S15Row1 :
    OAI.Laughlin.Certificate.yRow 17 7 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((640060726123211518125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S15Row2 :
    OAI.Laughlin.Certificate.yRow 17 7 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-2832562966462330448221875 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S15Row3 :
    OAI.Laughlin.Certificate.yRow 17 7 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((1070376552691963197305625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S15Row4 :
    OAI.Laughlin.Certificate.yRow 17 7 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((26526153718405351951565625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S15Row5 :
    OAI.Laughlin.Certificate.yRow 17 7 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((275458309012751746822565625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S15Row6 :
    OAI.Laughlin.Certificate.yRow 17 7 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((281117409070518173278125 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R7S15 :
    OAI.Laughlin.Certificate.errorRational 17 (3 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (3 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 7 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R7S15Row0,
    originalYRowSplitD17R7S15Row1,
    originalYRowSplitD17R7S15Row2,
    originalYRowSplitD17R7S15Row3,
    originalYRowSplitD17R7S15Row4,
    originalYRowSplitD17R7S15Row5,
    originalYRowSplitD17R7S15Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R7S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
