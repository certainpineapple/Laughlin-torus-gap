import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 7 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((-3670890702116855625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 7 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-28502538608116390869 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 7 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((2988849553778345597235 / 134217728) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 7 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-12918373159386147536445 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 7 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((3528819936117742548165 / 58720256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 7 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-29217720453316236095145 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 7 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-76772184534764046045 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R1S3 :
    OAI.Laughlin.Certificate.errorRational 7 (0 : Fin 4) (1 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (0 : Fin 4) (1 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R1S3Row0,
    originalYRowSplitD7R1S3Row1,
    originalYRowSplitD7R1S3Row2,
    originalYRowSplitD7R1S3Row3,
    originalYRowSplitD7R1S3Row4,
    originalYRowSplitD7R1S3Row5,
    originalYRowSplitD7R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
