import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 20 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 20 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 20 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 20 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 20 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((23795541239020989147084375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 20 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((489833988379768491834375 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 20 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((697567275040037273746875 / 32) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R7S7 :
    OAI.Laughlin.Certificate.errorRational 20 (3 : Fin 10) (3 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (3 : Fin 10) (3 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R7S7Row0,
    originalYRowSplitD20R7S7Row1,
    originalYRowSplitD20R7S7Row2,
    originalYRowSplitD20R7S7Row3,
    originalYRowSplitD20R7S7Row4,
    originalYRowSplitD20R7S7Row5,
    originalYRowSplitD20R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
