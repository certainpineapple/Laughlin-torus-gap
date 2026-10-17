import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R3S15Row0 :
    OAI.Laughlin.Certificate.yRow 15 3 15
      (OAI.Laughlin.Certificate.rows[0]!) = (-11309849433541631597625 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S15Row1 :
    OAI.Laughlin.Certificate.yRow 15 3 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((128540314457285458352625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S15Row2 :
    OAI.Laughlin.Certificate.yRow 15 3 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((608645390074166369696396625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S15Row3 :
    OAI.Laughlin.Certificate.yRow 15 3 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((-6138445896074080571857875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S15Row4 :
    OAI.Laughlin.Certificate.yRow 15 3 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((5830179693936473935434375 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S15Row5 :
    OAI.Laughlin.Certificate.yRow 15 3 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((272218747353831206186383125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S15Row6 :
    OAI.Laughlin.Certificate.yRow 15 3 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((3846599289045522091207125 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R3S15 :
    OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (1 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 3 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R3S15Row0,
    originalYRowSplitD15R3S15Row1,
    originalYRowSplitD15R3S15Row2,
    originalYRowSplitD15R3S15Row3,
    originalYRowSplitD15R3S15Row4,
    originalYRowSplitD15R3S15Row5,
    originalYRowSplitD15R3S15Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R3S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
