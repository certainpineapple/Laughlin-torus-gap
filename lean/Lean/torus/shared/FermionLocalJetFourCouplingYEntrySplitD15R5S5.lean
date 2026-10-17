import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 15 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = (-84362977132710451875 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 15 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((370816737999511505625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 15 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((22496540287944891151580625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 15 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((1987392602039246267000625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 15 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((82850280871224080666548125 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 15 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-281674717183392518169106875 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 15 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2484428811498284776689375 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R5S5 :
    OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (2 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (2 : Fin 8) (2 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R5S5Row0,
    originalYRowSplitD15R5S5Row1,
    originalYRowSplitD15R5S5Row2,
    originalYRowSplitD15R5S5Row3,
    originalYRowSplitD15R5S5Row4,
    originalYRowSplitD15R5S5Row5,
    originalYRowSplitD15R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
