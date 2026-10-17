import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD3R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 3 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((1100419980560787555 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 3 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((155481328833979996357 / 9395240960) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 3 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-54735576857653104496135 / 7516192768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 3 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-5683885258927607193053 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 3 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-5543911054522696276171 / 7516192768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 3 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((76120628321454710331713 / 30064771072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 3 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((35947816431289863681 / 268435456) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD3R1S3 :
    OAI.Laughlin.Certificate.errorRational 3 (0 : Fin 2) (1 : Fin 2) =
      TorusLean.FermionM3.errorTable03 (0 : Fin 2) (1 : Fin 2) := by
  change OAI.Laughlin.Certificate.Y 3 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD3R1S3Row0,
    originalYRowSplitD3R1S3Row1,
    originalYRowSplitD3R1S3Row2,
    originalYRowSplitD3R1S3Row3,
    originalYRowSplitD3R1S3Row4,
    originalYRowSplitD3R1S3Row5,
    originalYRowSplitD3R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable03]

#print axioms originalYEntrySplitD3R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
