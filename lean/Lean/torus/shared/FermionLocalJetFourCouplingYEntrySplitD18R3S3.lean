import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 18 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 18 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 18 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 18 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((1570460016008478382688525625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 18 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((55212631494016827923326859625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 18 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1741496828406043544369659125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 18 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-11505945294562367153328949125 / 131072) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R3S3 :
    OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (1 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (1 : Fin 9) (1 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R3S3Row0,
    originalYRowSplitD18R3S3Row1,
    originalYRowSplitD18R3S3Row2,
    originalYRowSplitD18R3S3Row3,
    originalYRowSplitD18R3S3Row4,
    originalYRowSplitD18R3S3Row5,
    originalYRowSplitD18R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
