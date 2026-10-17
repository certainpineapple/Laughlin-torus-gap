import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 13 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-1447812758766520989675 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 13 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-4492304077436493400575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 13 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-3976150332433499169119775 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 13 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-264188446536378790446975 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 13 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((984133206054954011239875 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 13 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((560089809735296631144975 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 13 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((299782593897866589458025 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R3S5 :
    OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (2 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (1 : Fin 7) (2 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R3S5Row0,
    originalYRowSplitD13R3S5Row1,
    originalYRowSplitD13R3S5Row2,
    originalYRowSplitD13R3S5Row3,
    originalYRowSplitD13R3S5Row4,
    originalYRowSplitD13R3S5Row5,
    originalYRowSplitD13R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
