import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD6R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 6 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((1894618221389866755 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 6 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-5906682592415661543 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 6 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-74768681741474967897795 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 6 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-10233307354108276259685 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 6 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-1237838441480291424975 / 134217728) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 6 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-7892199844173584455515 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 6 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((351997165245543497685 / 67108864) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD6R1S3 :
    OAI.Laughlin.Certificate.errorRational 6 (0 : Fin 3) (1 : Fin 3) =
      TorusLean.FermionM3.errorTable06 (0 : Fin 3) (1 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 6 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD6R1S3Row0,
    originalYRowSplitD6R1S3Row1,
    originalYRowSplitD6R1S3Row2,
    originalYRowSplitD6R1S3Row3,
    originalYRowSplitD6R1S3Row4,
    originalYRowSplitD6R1S3Row5,
    originalYRowSplitD6R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable06]

#print axioms originalYEntrySplitD6R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
