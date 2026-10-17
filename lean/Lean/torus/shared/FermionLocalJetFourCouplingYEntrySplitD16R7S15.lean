import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R7S15Row0 :
    OAI.Laughlin.Certificate.yRow 16 7 15
      (OAI.Laughlin.Certificate.rows[0]!) = (-49610294525399107500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S15Row1 :
    OAI.Laughlin.Certificate.yRow 16 7 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((696022722591936114375 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S15Row2 :
    OAI.Laughlin.Certificate.yRow 16 7 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-2285086626954285919639875 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S15Row3 :
    OAI.Laughlin.Certificate.yRow 16 7 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((2510938815341776551356625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S15Row4 :
    OAI.Laughlin.Certificate.yRow 16 7 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((674938076028011989318125 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S15Row5 :
    OAI.Laughlin.Certificate.yRow 16 7 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-54268629596648670704626125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S15Row6 :
    OAI.Laughlin.Certificate.yRow 16 7 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-9613613438707518615375 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R7S15 :
    OAI.Laughlin.Certificate.errorRational 16 (3 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (3 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 7 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R7S15Row0,
    originalYRowSplitD16R7S15Row1,
    originalYRowSplitD16R7S15Row2,
    originalYRowSplitD16R7S15Row3,
    originalYRowSplitD16R7S15Row4,
    originalYRowSplitD16R7S15Row5,
    originalYRowSplitD16R7S15Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R7S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
