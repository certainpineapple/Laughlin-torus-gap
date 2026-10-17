import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 15 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((228027970500915834243225 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 15 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((773972776812004576970625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 15 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((3677886039053979527353425 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 15 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-35775259061380272758206575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 15 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((165000004523742517653068325 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 15 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-294886746615023275400325 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 15 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-3291893013196543039116525 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R3S3 :
    OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (1 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (1 : Fin 8) (1 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R3S3Row0,
    originalYRowSplitD15R3S3Row1,
    originalYRowSplitD15R3S3Row2,
    originalYRowSplitD15R3S3Row3,
    originalYRowSplitD15R3S3Row4,
    originalYRowSplitD15R3S3Row5,
    originalYRowSplitD15R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
