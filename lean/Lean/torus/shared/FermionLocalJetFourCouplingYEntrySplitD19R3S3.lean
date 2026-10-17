import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 19 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 19 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 19 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 19 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 19 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((45477346231712334723608199375 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 19 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-172740102562647920049557432625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 19 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((1017080740498862843639710875 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R3S3 :
    OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (1 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (1 : Fin 10) (1 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R3S3Row0,
    originalYRowSplitD19R3S3Row1,
    originalYRowSplitD19R3S3Row2,
    originalYRowSplitD19R3S3Row3,
    originalYRowSplitD19R3S3Row4,
    originalYRowSplitD19R3S3Row5,
    originalYRowSplitD19R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
