import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 11 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((-110927235743234481375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 11 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((403497992460948451515 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 11 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-4114074129830729242552485 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 11 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-645843852633493376949825 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 11 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((6669113088221019150885 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 11 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-471928072218821848582245 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 11 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-3899914905520764136125 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R3S3 :
    OAI.Laughlin.Certificate.errorRational 11 (1 : Fin 6) (1 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (1 : Fin 6) (1 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R3S3Row0,
    originalYRowSplitD11R3S3Row1,
    originalYRowSplitD11R3S3Row2,
    originalYRowSplitD11R3S3Row3,
    originalYRowSplitD11R3S3Row4,
    originalYRowSplitD11R3S3Row5,
    originalYRowSplitD11R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
