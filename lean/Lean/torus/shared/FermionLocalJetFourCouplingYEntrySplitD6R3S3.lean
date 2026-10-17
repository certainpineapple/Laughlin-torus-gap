import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD6R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 6 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((2725734204556581627 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 6 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((330571801675250061 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 6 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((-2191737239677968804147 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 6 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-4250751716534374740915 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 6 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2501181682317239172591 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 6 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((43782869827913621003973 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 6 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-617610219448415791023 / 134217728) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD6R3S3 :
    OAI.Laughlin.Certificate.errorRational 6 (1 : Fin 3) (1 : Fin 3) =
      TorusLean.FermionM3.errorTable06 (1 : Fin 3) (1 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 6 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD6R3S3Row0,
    originalYRowSplitD6R3S3Row1,
    originalYRowSplitD6R3S3Row2,
    originalYRowSplitD6R3S3Row3,
    originalYRowSplitD6R3S3Row4,
    originalYRowSplitD6R3S3Row5,
    originalYRowSplitD6R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable06]

#print axioms originalYEntrySplitD6R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
