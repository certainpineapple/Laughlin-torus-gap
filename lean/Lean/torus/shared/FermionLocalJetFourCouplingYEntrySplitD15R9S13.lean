import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R9S13Row0 :
    OAI.Laughlin.Certificate.yRow 15 9 13
      (OAI.Laughlin.Certificate.rows[0]!) = (2587628882296778720400 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S13Row1 :
    OAI.Laughlin.Certificate.yRow 15 9 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-746771313843488708775 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S13Row2 :
    OAI.Laughlin.Certificate.yRow 15 9 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((152014616772431171583825 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S13Row3 :
    OAI.Laughlin.Certificate.yRow 15 9 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-619162108835424024145275 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S13Row4 :
    OAI.Laughlin.Certificate.yRow 15 9 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3589992989385504605271225 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S13Row5 :
    OAI.Laughlin.Certificate.yRow 15 9 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2576894493891694755732525 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S13Row6 :
    OAI.Laughlin.Certificate.yRow 15 9 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-9304912552938515788275 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R9S13 :
    OAI.Laughlin.Certificate.errorRational 15 (4 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (4 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 9 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R9S13Row0,
    originalYRowSplitD15R9S13Row1,
    originalYRowSplitD15R9S13Row2,
    originalYRowSplitD15R9S13Row3,
    originalYRowSplitD15R9S13Row4,
    originalYRowSplitD15R9S13Row5,
    originalYRowSplitD15R9S13Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R9S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
