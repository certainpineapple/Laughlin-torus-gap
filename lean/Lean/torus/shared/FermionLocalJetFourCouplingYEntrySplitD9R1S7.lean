import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 9 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-76851542515528362645 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 9 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((17975298592085848749 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 9 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((116718831627717397300965 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 9 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-935714189775798315855 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 9 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((13449554030020925712465 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 9 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-467940505913422178713545 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 9 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((242542306261443315645 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R1S7 :
    OAI.Laughlin.Certificate.errorRational 9 (0 : Fin 5) (3 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (0 : Fin 5) (3 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R1S7Row0,
    originalYRowSplitD9R1S7Row1,
    originalYRowSplitD9R1S7Row2,
    originalYRowSplitD9R1S7Row3,
    originalYRowSplitD9R1S7Row4,
    originalYRowSplitD9R1S7Row5,
    originalYRowSplitD9R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
