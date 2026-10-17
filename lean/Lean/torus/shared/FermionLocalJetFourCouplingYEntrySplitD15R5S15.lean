import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R5S15Row0 :
    OAI.Laughlin.Certificate.yRow 15 5 15
      (OAI.Laughlin.Certificate.rows[0]!) = (-14976871088114745810000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S15Row1 :
    OAI.Laughlin.Certificate.yRow 15 5 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((57742436618982175685625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S15Row2 :
    OAI.Laughlin.Certificate.yRow 15 5 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-226026336384372559690029375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S15Row3 :
    OAI.Laughlin.Certificate.yRow 15 5 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((4997597066397430274154375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S15Row4 :
    OAI.Laughlin.Certificate.yRow 15 5 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((7237502083364861203520625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S15Row5 :
    OAI.Laughlin.Certificate.yRow 15 5 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-44091343062501515993086875 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S15Row6 :
    OAI.Laughlin.Certificate.yRow 15 5 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((76527175118117189090625 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R5S15 :
    OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (2 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 5 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R5S15Row0,
    originalYRowSplitD15R5S15Row1,
    originalYRowSplitD15R5S15Row2,
    originalYRowSplitD15R5S15Row3,
    originalYRowSplitD15R5S15Row4,
    originalYRowSplitD15R5S15Row5,
    originalYRowSplitD15R5S15Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R5S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
