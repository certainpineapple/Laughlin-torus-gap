import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD5R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 5 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((517229739078330765 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 5 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((33354143675585625297 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 5 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-39698825671225989422295 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 5 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-24352127547028721893585 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 5 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-18686933965106262007505 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 5 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((209580109115659324643705 / 3758096384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 5 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((122766324303368643735 / 67108864) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD5R1S5 :
    OAI.Laughlin.Certificate.errorRational 5 (0 : Fin 3) (2 : Fin 3) =
      TorusLean.FermionM3.errorTable05 (0 : Fin 3) (2 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 5 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD5R1S5Row0,
    originalYRowSplitD5R1S5Row1,
    originalYRowSplitD5R1S5Row2,
    originalYRowSplitD5R1S5Row3,
    originalYRowSplitD5R1S5Row4,
    originalYRowSplitD5R1S5Row5,
    originalYRowSplitD5R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable05]

#print axioms originalYEntrySplitD5R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
