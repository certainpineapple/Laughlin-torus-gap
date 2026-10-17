import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 11 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-7236471023872764975 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 11 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((54431263395018371835 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 11 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-30842104294118183003685 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 11 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((14371340118343316208135 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 11 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((26330568708746192680845 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 11 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((812189509660634191179885 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 11 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1136497251661494345315 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R7S7 :
    OAI.Laughlin.Certificate.errorRational 11 (3 : Fin 6) (3 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (3 : Fin 6) (3 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R7S7Row0,
    originalYRowSplitD11R7S7Row1,
    originalYRowSplitD11R7S7Row2,
    originalYRowSplitD11R7S7Row3,
    originalYRowSplitD11R7S7Row4,
    originalYRowSplitD11R7S7Row5,
    originalYRowSplitD11R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
