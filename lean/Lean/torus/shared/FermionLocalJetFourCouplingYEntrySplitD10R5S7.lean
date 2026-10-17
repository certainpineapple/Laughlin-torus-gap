import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 10 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((11945011935383731575 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 10 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((8134856516591286075 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 10 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((26586017464599759243375 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 10 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((2643383572940738742975 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 10 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-4505859245842609962825 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 10 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((455788813197417519951675 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 10 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((737405701243471031625 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R5S7 :
    OAI.Laughlin.Certificate.errorRational 10 (2 : Fin 5) (3 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (2 : Fin 5) (3 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R5S7Row0,
    originalYRowSplitD10R5S7Row1,
    originalYRowSplitD10R5S7Row2,
    originalYRowSplitD10R5S7Row3,
    originalYRowSplitD10R5S7Row4,
    originalYRowSplitD10R5S7Row5,
    originalYRowSplitD10R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
