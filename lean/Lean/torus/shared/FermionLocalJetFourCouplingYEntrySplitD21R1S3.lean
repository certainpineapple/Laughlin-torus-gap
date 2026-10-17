import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 21 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 21 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 21 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 21 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 21 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2526659220685768849331286260625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 21 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-622213106921091813304051875 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 21 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((175598940591968524656382231875 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R1S3 :
    OAI.Laughlin.Certificate.errorRational 21 (0 : Fin 11) (1 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (0 : Fin 11) (1 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R1S3Row0,
    originalYRowSplitD21R1S3Row1,
    originalYRowSplitD21R1S3Row2,
    originalYRowSplitD21R1S3Row3,
    originalYRowSplitD21R1S3Row4,
    originalYRowSplitD21R1S3Row5,
    originalYRowSplitD21R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
