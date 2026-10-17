import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 7 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((1339467956678017935 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 7 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((6048833004624160083 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 7 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((21081146259965870818659 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 7 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((11539020213471479679117 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 7 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((5238129656277557731281 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 7 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((44738130881813395918293 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 7 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-61880973868094171805 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R3S3 :
    OAI.Laughlin.Certificate.errorRational 7 (1 : Fin 4) (1 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (1 : Fin 4) (1 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R3S3Row0,
    originalYRowSplitD7R3S3Row1,
    originalYRowSplitD7R3S3Row2,
    originalYRowSplitD7R3S3Row3,
    originalYRowSplitD7R3S3Row4,
    originalYRowSplitD7R3S3Row5,
    originalYRowSplitD7R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
