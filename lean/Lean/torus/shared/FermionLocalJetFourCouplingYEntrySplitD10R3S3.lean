import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 10 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((33590047376779277895 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 10 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-38462455927212336945 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 10 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-429497723146463840669985 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 10 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-153391120765439617104165 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 10 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((90261965538709439856075 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 10 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((1250249630066209723905 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 10 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-91593531752403750316695 / 16777216) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R3S3 :
    OAI.Laughlin.Certificate.errorRational 10 (1 : Fin 5) (1 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (1 : Fin 5) (1 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R3S3Row0,
    originalYRowSplitD10R3S3Row1,
    originalYRowSplitD10R3S3Row2,
    originalYRowSplitD10R3S3Row3,
    originalYRowSplitD10R3S3Row4,
    originalYRowSplitD10R3S3Row5,
    originalYRowSplitD10R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
