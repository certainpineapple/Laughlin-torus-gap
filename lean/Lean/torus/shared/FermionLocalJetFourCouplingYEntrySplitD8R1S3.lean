import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 8 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((-11387494346113586295 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 8 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((197119650262423977 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 8 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((36872577681837689686995 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 8 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((15064379418747419024745 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 8 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-441299603451117593115 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 8 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-6630239381949782627055 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 8 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-397903947246140783805 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R1S3 :
    OAI.Laughlin.Certificate.errorRational 8 (0 : Fin 4) (1 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (0 : Fin 4) (1 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R1S3Row0,
    originalYRowSplitD8R1S3Row1,
    originalYRowSplitD8R1S3Row2,
    originalYRowSplitD8R1S3Row3,
    originalYRowSplitD8R1S3Row4,
    originalYRowSplitD8R1S3Row5,
    originalYRowSplitD8R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
