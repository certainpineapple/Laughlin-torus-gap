import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 14 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-789423196101323494725 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 14 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((852295944374092050525 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 14 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((1487004239934921803393025 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 14 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-261186745154168548831725 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 14 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((177933782129111426216925 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 14 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-10171048550388560104887225 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 14 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((9054399053420791656075 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R5S7 :
    OAI.Laughlin.Certificate.errorRational 14 (2 : Fin 7) (3 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (2 : Fin 7) (3 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R5S7Row0,
    originalYRowSplitD14R5S7Row1,
    originalYRowSplitD14R5S7Row2,
    originalYRowSplitD14R5S7Row3,
    originalYRowSplitD14R5S7Row4,
    originalYRowSplitD14R5S7Row5,
    originalYRowSplitD14R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
