import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R7S15Row0 :
    OAI.Laughlin.Certificate.yRow 19 7 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S15Row1 :
    OAI.Laughlin.Certificate.yRow 19 7 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S15Row2 :
    OAI.Laughlin.Certificate.yRow 19 7 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S15Row3 :
    OAI.Laughlin.Certificate.yRow 19 7 15
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S15Row4 :
    OAI.Laughlin.Certificate.yRow 19 7 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((305313804271762254584240625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S15Row5 :
    OAI.Laughlin.Certificate.yRow 19 7 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-989675071809729227807259375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R7S15Row6 :
    OAI.Laughlin.Certificate.yRow 19 7 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-66443174223042323581875 / 8) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R7S15 :
    OAI.Laughlin.Certificate.errorRational 19 (3 : Fin 10) (7 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (3 : Fin 10) (7 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 7 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R7S15Row0,
    originalYRowSplitD19R7S15Row1,
    originalYRowSplitD19R7S15Row2,
    originalYRowSplitD19R7S15Row3,
    originalYRowSplitD19R7S15Row4,
    originalYRowSplitD19R7S15Row5,
    originalYRowSplitD19R7S15Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R7S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
