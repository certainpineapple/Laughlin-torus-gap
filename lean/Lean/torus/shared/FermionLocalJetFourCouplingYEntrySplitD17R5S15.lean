import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R5S15Row0 :
    OAI.Laughlin.Certificate.yRow 17 5 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S15Row1 :
    OAI.Laughlin.Certificate.yRow 17 5 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-10926747445897792884375 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S15Row2 :
    OAI.Laughlin.Certificate.yRow 17 5 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((5644674604808190494668125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S15Row3 :
    OAI.Laughlin.Certificate.yRow 17 5 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((-267976013029688132544375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S15Row4 :
    OAI.Laughlin.Certificate.yRow 17 5 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-58130442753401332060621875 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S15Row5 :
    OAI.Laughlin.Certificate.yRow 17 5 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-812038642319151720025678125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S15Row6 :
    OAI.Laughlin.Certificate.yRow 17 5 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-44041208149716846193125 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R5S15 :
    OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (2 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 5 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R5S15Row0,
    originalYRowSplitD17R5S15Row1,
    originalYRowSplitD17R5S15Row2,
    originalYRowSplitD17R5S15Row3,
    originalYRowSplitD17R5S15Row4,
    originalYRowSplitD17R5S15Row5,
    originalYRowSplitD17R5S15Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R5S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
