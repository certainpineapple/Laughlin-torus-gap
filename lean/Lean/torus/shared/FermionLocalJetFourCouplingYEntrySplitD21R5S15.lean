import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R5S15Row0 :
    OAI.Laughlin.Certificate.yRow 21 5 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S15Row1 :
    OAI.Laughlin.Certificate.yRow 21 5 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S15Row2 :
    OAI.Laughlin.Certificate.yRow 21 5 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S15Row3 :
    OAI.Laughlin.Certificate.yRow 21 5 15
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S15Row4 :
    OAI.Laughlin.Certificate.yRow 21 5 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((111272099872191694532971875 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S15Row5 :
    OAI.Laughlin.Certificate.yRow 21 5 15
      (OAI.Laughlin.Certificate.rows[5]!) = (-8329706586580829650200000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S15Row6 :
    OAI.Laughlin.Certificate.yRow 21 5 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R5S15 :
    OAI.Laughlin.Certificate.errorRational 21 (2 : Fin 11) (7 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (2 : Fin 11) (7 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 5 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R5S15Row0,
    originalYRowSplitD21R5S15Row1,
    originalYRowSplitD21R5S15Row2,
    originalYRowSplitD21R5S15Row3,
    originalYRowSplitD21R5S15Row4,
    originalYRowSplitD21R5S15Row5,
    originalYRowSplitD21R5S15Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R5S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
