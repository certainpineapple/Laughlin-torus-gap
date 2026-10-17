import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R1S3Row0 :
    OAI.Laughlin.Certificate.yRow 10 1 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((211055037100150862745 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S3Row1 :
    OAI.Laughlin.Certificate.yRow 10 1 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((697858877933391587355 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S3Row2 :
    OAI.Laughlin.Certificate.yRow 10 1 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((2233331794112107902998895 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S3Row3 :
    OAI.Laughlin.Certificate.yRow 10 1 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((1163304013723901845509375 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S3Row4 :
    OAI.Laughlin.Certificate.yRow 10 1 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((15877896421527891446895 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S3Row5 :
    OAI.Laughlin.Certificate.yRow 10 1 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((1142563183016430075341625 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S3Row6 :
    OAI.Laughlin.Certificate.yRow 10 1 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((46691394983709432649875 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R1S3 :
    OAI.Laughlin.Certificate.errorRational 10 (0 : Fin 5) (1 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (0 : Fin 5) (1 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 1 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R1S3Row0,
    originalYRowSplitD10R1S3Row1,
    originalYRowSplitD10R1S3Row2,
    originalYRowSplitD10R1S3Row3,
    originalYRowSplitD10R1S3Row4,
    originalYRowSplitD10R1S3Row5,
    originalYRowSplitD10R1S3Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R1S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
