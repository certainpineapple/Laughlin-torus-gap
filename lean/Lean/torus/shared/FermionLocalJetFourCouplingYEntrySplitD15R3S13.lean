import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R3S13Row0 :
    OAI.Laughlin.Certificate.yRow 15 3 13
      (OAI.Laughlin.Certificate.rows[0]!) = (-6952421273205933825300 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S13Row1 :
    OAI.Laughlin.Certificate.yRow 15 3 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-8002700539333861335975 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S13Row2 :
    OAI.Laughlin.Certificate.yRow 15 3 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((10411592607440960255345025 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S13Row3 :
    OAI.Laughlin.Certificate.yRow 15 3 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-2562670953982209332787525 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S13Row4 :
    OAI.Laughlin.Certificate.yRow 15 3 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((11838492254902300005865275 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S13Row5 :
    OAI.Laughlin.Certificate.yRow 15 3 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-8502652397729730199813425 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S13Row6 :
    OAI.Laughlin.Certificate.yRow 15 3 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2065812346142094280655925 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R3S13 :
    OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (1 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 3 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R3S13Row0,
    originalYRowSplitD15R3S13Row1,
    originalYRowSplitD15R3S13Row2,
    originalYRowSplitD15R3S13Row3,
    originalYRowSplitD15R3S13Row4,
    originalYRowSplitD15R3S13Row5,
    originalYRowSplitD15R3S13Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R3S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
