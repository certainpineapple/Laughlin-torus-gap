import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 20 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 20 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 20 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 20 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 20 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-35222047785264776243179246875 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 20 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-389819535093575272334273625 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 20 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((5623477505297593475004095625 / 32) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R1S3 :
    OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (1 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (0 : Fin 10) (1 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R1S3Row0,
    originalYRowSplitD20R1S3Row1,
    originalYRowSplitD20R1S3Row2,
    originalYRowSplitD20R1S3Row3,
    originalYRowSplitD20R1S3Row4,
    originalYRowSplitD20R1S3Row5,
    originalYRowSplitD20R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
