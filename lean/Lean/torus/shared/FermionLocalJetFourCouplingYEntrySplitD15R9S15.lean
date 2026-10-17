import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R9S15Row0 :
    OAI.Laughlin.Certificate.yRow 15 9 15
      (OAI.Laughlin.Certificate.rows[0]!) = (-4417057702795339602000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S15Row1 :
    OAI.Laughlin.Certificate.yRow 15 9 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-3234258085120900212375 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S15Row2 :
    OAI.Laughlin.Certificate.yRow 15 9 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-35074364526622489819125375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S15Row3 :
    OAI.Laughlin.Certificate.yRow 15 9 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((43818200767315079980875 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S15Row4 :
    OAI.Laughlin.Certificate.yRow 15 9 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-540004470430409311201875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S15Row5 :
    OAI.Laughlin.Certificate.yRow 15 9 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((12689438495243661261235125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S15Row6 :
    OAI.Laughlin.Certificate.yRow 15 9 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1208057713146224065125 / 32) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R9S15 :
    OAI.Laughlin.Certificate.errorRational 15 (4 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (4 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 9 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R9S15Row0,
    originalYRowSplitD15R9S15Row1,
    originalYRowSplitD15R9S15Row2,
    originalYRowSplitD15R9S15Row3,
    originalYRowSplitD15R9S15Row4,
    originalYRowSplitD15R9S15Row5,
    originalYRowSplitD15R9S15Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R9S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
