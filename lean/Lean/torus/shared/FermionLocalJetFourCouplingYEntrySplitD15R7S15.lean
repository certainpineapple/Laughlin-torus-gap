import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R7S15Row0 :
    OAI.Laughlin.Certificate.yRow 15 7 15
      (OAI.Laughlin.Certificate.rows[0]!) = (-3966631715227737055500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S15Row1 :
    OAI.Laughlin.Certificate.yRow 15 7 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-8506871435600628465375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S15Row2 :
    OAI.Laughlin.Certificate.yRow 15 7 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-28411096714200487515603375 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S15Row3 :
    OAI.Laughlin.Certificate.yRow 15 7 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((-2308321799021953062723375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S15Row4 :
    OAI.Laughlin.Certificate.yRow 15 7 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-7253209059016695047398125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S15Row5 :
    OAI.Laughlin.Certificate.yRow 15 7 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-66351817135632104926975125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S15Row6 :
    OAI.Laughlin.Certificate.yRow 15 7 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2435877378998404716375 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R7S15 :
    OAI.Laughlin.Certificate.errorRational 15 (3 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (3 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 7 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R7S15Row0,
    originalYRowSplitD15R7S15Row1,
    originalYRowSplitD15R7S15Row2,
    originalYRowSplitD15R7S15Row3,
    originalYRowSplitD15R7S15Row4,
    originalYRowSplitD15R7S15Row5,
    originalYRowSplitD15R7S15Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R7S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
