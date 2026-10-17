import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD4R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 4 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((1327535101841073453 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 4 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-18168448971436132277 / 1174405120) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 4 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((9875393438864549575115 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 4 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-10194063043441774359351 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 4 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((5653549732089275620507 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 4 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((11048807723939186013839 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD4R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 4 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-244048833283258029951 / 268435456) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD4R3S3 :
    OAI.Laughlin.Certificate.errorRational 4 (1 : Fin 2) (1 : Fin 2) =
      TorusLean.FermionM3.errorTable04 (1 : Fin 2) (1 : Fin 2) := by
  change OAI.Laughlin.Certificate.Y 4 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD4R3S3Row0,
    originalYRowSplitD4R3S3Row1,
    originalYRowSplitD4R3S3Row2,
    originalYRowSplitD4R3S3Row3,
    originalYRowSplitD4R3S3Row4,
    originalYRowSplitD4R3S3Row5,
    originalYRowSplitD4R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable04]

#print axioms originalYEntrySplitD4R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
