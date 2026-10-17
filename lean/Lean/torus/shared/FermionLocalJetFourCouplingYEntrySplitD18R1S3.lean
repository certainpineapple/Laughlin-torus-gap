import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 18 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 18 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 18 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 18 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-2929177757894099241683278125 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 18 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-118999705281209853163761072375 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 18 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((145851731583030064410801357375 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 18 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((21660326208488855335400827875 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R1S3 :
    OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (1 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (0 : Fin 9) (1 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R1S3Row0,
    originalYRowSplitD18R1S3Row1,
    originalYRowSplitD18R1S3Row2,
    originalYRowSplitD18R1S3Row3,
    originalYRowSplitD18R1S3Row4,
    originalYRowSplitD18R1S3Row5,
    originalYRowSplitD18R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
