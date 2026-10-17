import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 9 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((137998460609600895 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 9 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((5464962054304085781 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 9 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((31850012339035273371285 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 9 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((1024794871076689063755 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 9 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-21261190669797997198185 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 9 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((458049181616191354959975 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 9 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1614592754917748038755 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R5S5 :
    OAI.Laughlin.Certificate.errorRational 9 (2 : Fin 5) (2 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (2 : Fin 5) (2 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R5S5Row0,
    originalYRowSplitD9R5S5Row1,
    originalYRowSplitD9R5S5Row2,
    originalYRowSplitD9R5S5Row3,
    originalYRowSplitD9R5S5Row4,
    originalYRowSplitD9R5S5Row5,
    originalYRowSplitD9R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
