import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 7 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-1488415248143087355 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 7 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((9225871950243624195 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 7 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-3990280684502974026525 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 7 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-6304209573025048032825 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 7 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-1462389462807293524305 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 7 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((51986196748062068309475 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 7 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((47466735597972069435 / 1048576) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R3S7 :
    OAI.Laughlin.Certificate.errorRational 7 (1 : Fin 4) (3 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (1 : Fin 4) (3 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R3S7Row0,
    originalYRowSplitD7R3S7Row1,
    originalYRowSplitD7R3S7Row2,
    originalYRowSplitD7R3S7Row3,
    originalYRowSplitD7R3S7Row4,
    originalYRowSplitD7R3S7Row5,
    originalYRowSplitD7R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
