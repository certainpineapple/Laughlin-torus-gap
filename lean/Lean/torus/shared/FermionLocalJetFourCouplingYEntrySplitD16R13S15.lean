import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R13S15Row0 :
    OAI.Laughlin.Certificate.yRow 16 13 15
      (OAI.Laughlin.Certificate.rows[0]!) = (21858660855293502240000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S15Row1 :
    OAI.Laughlin.Certificate.yRow 16 13 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-462606376191995660625 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S15Row2 :
    OAI.Laughlin.Certificate.yRow 16 13 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-370447450608644122588875 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S15Row3 :
    OAI.Laughlin.Certificate.yRow 16 13 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((3705943771782036179269875 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S15Row4 :
    OAI.Laughlin.Certificate.yRow 16 13 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((8807303278805883534057375 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S15Row5 :
    OAI.Laughlin.Certificate.yRow 16 13 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-10443095392619623406297625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R13S15Row6 :
    OAI.Laughlin.Certificate.yRow 16 13 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R13S15 :
    OAI.Laughlin.Certificate.errorRational 16 (6 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (6 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 13 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R13S15Row0,
    originalYRowSplitD16R13S15Row1,
    originalYRowSplitD16R13S15Row2,
    originalYRowSplitD16R13S15Row3,
    originalYRowSplitD16R13S15Row4,
    originalYRowSplitD16R13S15Row5,
    originalYRowSplitD16R13S15Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R13S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
