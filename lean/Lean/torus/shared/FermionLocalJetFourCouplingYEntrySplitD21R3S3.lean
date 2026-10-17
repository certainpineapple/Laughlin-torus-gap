import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 21 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 21 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 21 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 21 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 21 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((464206726648855935894157383375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 21 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((287678121292517005455780375 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 21 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-16635689108712807599025685125 / 32) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R3S3 :
    OAI.Laughlin.Certificate.errorRational 21 (1 : Fin 11) (1 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (1 : Fin 11) (1 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R3S3Row0,
    originalYRowSplitD21R3S3Row1,
    originalYRowSplitD21R3S3Row2,
    originalYRowSplitD21R3S3Row3,
    originalYRowSplitD21R3S3Row4,
    originalYRowSplitD21R3S3Row5,
    originalYRowSplitD21R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
