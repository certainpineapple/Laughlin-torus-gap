import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R7S13Row0 :
    OAI.Laughlin.Certificate.yRow 15 7 13
      (OAI.Laughlin.Certificate.rows[0]!) = (1385766998794604626200 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S13Row1 :
    OAI.Laughlin.Certificate.yRow 15 7 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-78727506154169847975 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S13Row2 :
    OAI.Laughlin.Certificate.yRow 15 7 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-3194130588859523112774975 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S13Row3 :
    OAI.Laughlin.Certificate.yRow 15 7 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((131554133264653227703575 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S13Row4 :
    OAI.Laughlin.Certificate.yRow 15 7 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((9866899196913752254886625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S13Row5 :
    OAI.Laughlin.Certificate.yRow 15 7 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-12180980776842869391875475 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S13Row6 :
    OAI.Laughlin.Certificate.yRow 15 7 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((2777783627228587552575 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R7S13 :
    OAI.Laughlin.Certificate.errorRational 15 (3 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (3 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 7 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R7S13Row0,
    originalYRowSplitD15R7S13Row1,
    originalYRowSplitD15R7S13Row2,
    originalYRowSplitD15R7S13Row3,
    originalYRowSplitD15R7S13Row4,
    originalYRowSplitD15R7S13Row5,
    originalYRowSplitD15R7S13Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R7S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
