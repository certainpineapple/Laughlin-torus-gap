import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R11S15Row0 :
    OAI.Laughlin.Certificate.yRow 21 11 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S15Row1 :
    OAI.Laughlin.Certificate.yRow 21 11 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S15Row2 :
    OAI.Laughlin.Certificate.yRow 21 11 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S15Row3 :
    OAI.Laughlin.Certificate.yRow 21 11 15
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S15Row4 :
    OAI.Laughlin.Certificate.yRow 21 11 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-6035141437959013295540625 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S15Row5 :
    OAI.Laughlin.Certificate.yRow 21 11 15
      (OAI.Laughlin.Certificate.rows[5]!) = (4328230881655273893300000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S15Row6 :
    OAI.Laughlin.Certificate.yRow 21 11 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R11S15 :
    OAI.Laughlin.Certificate.errorRational 21 (5 : Fin 11) (7 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (5 : Fin 11) (7 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 11 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R11S15Row0,
    originalYRowSplitD21R11S15Row1,
    originalYRowSplitD21R11S15Row2,
    originalYRowSplitD21R11S15Row3,
    originalYRowSplitD21R11S15Row4,
    originalYRowSplitD21R11S15Row5,
    originalYRowSplitD21R11S15Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R11S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
