import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 14 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((793650685861555880883525 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 14 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-124770328316466908350275 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 14 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-912761483323238037553038975 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 14 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((58737518798874836412395475 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 14 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-319043100334127928764180175 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 14 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((368842707994683457629569475 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 14 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-6743183250145259272179825 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R1S3 :
    OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (1 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (0 : Fin 7) (1 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R1S3Row0,
    originalYRowSplitD14R1S3Row1,
    originalYRowSplitD14R1S3Row2,
    originalYRowSplitD14R1S3Row3,
    originalYRowSplitD14R1S3Row4,
    originalYRowSplitD14R1S3Row5,
    originalYRowSplitD14R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
