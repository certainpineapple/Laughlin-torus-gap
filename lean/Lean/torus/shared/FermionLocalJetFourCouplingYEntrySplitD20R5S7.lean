import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 20 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 20 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 20 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 20 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 20 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((94124137992358826567840625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 20 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2684250842349009799490625 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 20 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-3487836375200186368734375 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R5S7 :
    OAI.Laughlin.Certificate.errorRational 20 (2 : Fin 10) (3 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (2 : Fin 10) (3 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R5S7Row0,
    originalYRowSplitD20R5S7Row1,
    originalYRowSplitD20R5S7Row2,
    originalYRowSplitD20R5S7Row3,
    originalYRowSplitD20R5S7Row4,
    originalYRowSplitD20R5S7Row5,
    originalYRowSplitD20R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
