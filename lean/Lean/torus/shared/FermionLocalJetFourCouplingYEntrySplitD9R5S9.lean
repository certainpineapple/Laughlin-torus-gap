import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 9 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-3896320674987089055 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 9 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((17375317532420338701 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 9 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((15897950149643001491445 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 9 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-14688513050811775464465 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 9 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-13421199302434643751855 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 9 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((47148672025377654368625 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 9 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-647299710956609130105 / 1048576) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R5S9 :
    OAI.Laughlin.Certificate.errorRational 9 (2 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (2 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R5S9Row0,
    originalYRowSplitD9R5S9Row1,
    originalYRowSplitD9R5S9Row2,
    originalYRowSplitD9R5S9Row3,
    originalYRowSplitD9R5S9Row4,
    originalYRowSplitD9R5S9Row5,
    originalYRowSplitD9R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
