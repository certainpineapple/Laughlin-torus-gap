import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R1S15Row0 :
    OAI.Laughlin.Certificate.yRow 18 1 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S15Row1 :
    OAI.Laughlin.Certificate.yRow 18 1 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S15Row2 :
    OAI.Laughlin.Certificate.yRow 18 1 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S15Row3 :
    OAI.Laughlin.Certificate.yRow 18 1 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((51553678126663208880759375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S15Row4 :
    OAI.Laughlin.Certificate.yRow 18 1 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((11206999147156452066301875 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S15Row5 :
    OAI.Laughlin.Certificate.yRow 18 1 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((1177588073735185995174166875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S15Row6 :
    OAI.Laughlin.Certificate.yRow 18 1 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((136769184025191236112969375 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R1S15 :
    OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (0 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 1 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R1S15Row0,
    originalYRowSplitD18R1S15Row1,
    originalYRowSplitD18R1S15Row2,
    originalYRowSplitD18R1S15Row3,
    originalYRowSplitD18R1S15Row4,
    originalYRowSplitD18R1S15Row5,
    originalYRowSplitD18R1S15Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R1S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
