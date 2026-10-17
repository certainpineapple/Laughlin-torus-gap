import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD5R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 5 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((1227892611554313699 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 5 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-40217208208139155215 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 5 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((3609794378028611869977 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 5 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((15972179718835785494373 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 5 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((973139460225276068975 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 5 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((8556207819014717270965 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 5 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-26195139147988314471 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD5R1S3 :
    OAI.Laughlin.Certificate.errorRational 5 (0 : Fin 3) (1 : Fin 3) =
      TorusLean.FermionM3.errorTable05 (0 : Fin 3) (1 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 5 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD5R1S3Row0,
    originalYRowSplitD5R1S3Row1,
    originalYRowSplitD5R1S3Row2,
    originalYRowSplitD5R1S3Row3,
    originalYRowSplitD5R1S3Row4,
    originalYRowSplitD5R1S3Row5,
    originalYRowSplitD5R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable05]

#print axioms originalYEntrySplitD5R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
