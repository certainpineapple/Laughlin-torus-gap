import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 15 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((-2019580538806076820148575 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 15 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-7662147028217219890927575 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 15 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((12319248955920178812072357825 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 15 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((370897535910488764737534975 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 15 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-253149389883003214313888175 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 15 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-5313210495846343907423381775 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 15 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((4165084270547719886141775 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R1S3 :
    OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (1 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (0 : Fin 8) (1 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R1S3Row0,
    originalYRowSplitD15R1S3Row1,
    originalYRowSplitD15R1S3Row2,
    originalYRowSplitD15R1S3Row3,
    originalYRowSplitD15R1S3Row4,
    originalYRowSplitD15R1S3Row5,
    originalYRowSplitD15R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
