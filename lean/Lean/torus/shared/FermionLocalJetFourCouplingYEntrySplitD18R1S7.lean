import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 18 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 18 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 18 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 18 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((54253522692637157924409375 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 18 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-5808030622286151823076638125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 18 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((65038163242863713093799733125 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 18 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-585735377267170963538330625 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R1S7 :
    OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (3 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (0 : Fin 9) (3 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R1S7Row0,
    originalYRowSplitD18R1S7Row1,
    originalYRowSplitD18R1S7Row2,
    originalYRowSplitD18R1S7Row3,
    originalYRowSplitD18R1S7Row4,
    originalYRowSplitD18R1S7Row5,
    originalYRowSplitD18R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
