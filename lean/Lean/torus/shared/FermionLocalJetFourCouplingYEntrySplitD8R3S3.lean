import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 8 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((15977720834090203455 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 8 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((3142036540605854661 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 8 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((685667686484171871195 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 8 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-18744793144766932510845 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 8 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-6097593366856360539375 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 8 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((32391427003169138594775 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 8 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1988696899266245149545 / 33554432) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R3S3 :
    OAI.Laughlin.Certificate.errorRational 8 (1 : Fin 4) (1 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (1 : Fin 4) (1 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R3S3Row0,
    originalYRowSplitD8R3S3Row1,
    originalYRowSplitD8R3S3Row2,
    originalYRowSplitD8R3S3Row3,
    originalYRowSplitD8R3S3Row4,
    originalYRowSplitD8R3S3Row5,
    originalYRowSplitD8R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
