import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD5R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 5 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((828106156763491761 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 5 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((12057655206433421045 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 5 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-6457052018534822018791 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 5 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((885506700796361417871 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 5 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-543574257899971267101 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 5 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((10662554367612487256863 / 268435456) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 5 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-175521550402232335797 / 67108864) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD5R3S3 :
    OAI.Laughlin.Certificate.errorRational 5 (1 : Fin 3) (1 : Fin 3) =
      TorusLean.FermionM3.errorTable05 (1 : Fin 3) (1 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 5 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD5R3S3Row0,
    originalYRowSplitD5R3S3Row1,
    originalYRowSplitD5R3S3Row2,
    originalYRowSplitD5R3S3Row3,
    originalYRowSplitD5R3S3Row4,
    originalYRowSplitD5R3S3Row5,
    originalYRowSplitD5R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable05]

#print axioms originalYEntrySplitD5R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
