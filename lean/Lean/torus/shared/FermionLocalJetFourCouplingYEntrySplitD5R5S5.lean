import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD5R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 5 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((2127370824716077635 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 5 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((105906315909713386913 / 58720256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 5 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((79674709640186975436905 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 5 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((16556987918363989467635 / 58720256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 5 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((35865503886652808531045 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 5 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((52813174350218993123795 / 536870912) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 5 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-465607554421578820545 / 67108864) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD5R5S5 :
    OAI.Laughlin.Certificate.errorRational 5 (2 : Fin 3) (2 : Fin 3) =
      TorusLean.FermionM3.errorTable05 (2 : Fin 3) (2 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 5 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD5R5S5Row0,
    originalYRowSplitD5R5S5Row1,
    originalYRowSplitD5R5S5Row2,
    originalYRowSplitD5R5S5Row3,
    originalYRowSplitD5R5S5Row4,
    originalYRowSplitD5R5S5Row5,
    originalYRowSplitD5R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable05]

#print axioms originalYEntrySplitD5R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
