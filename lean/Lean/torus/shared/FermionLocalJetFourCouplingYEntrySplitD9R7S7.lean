import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 9 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((9675551912051934405 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 9 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-3465709964343838989 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 9 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((14167501657242728863725 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 9 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((549970250068154322225 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 9 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-5193440717787808155435 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 9 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((124158926843089489970865 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 9 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-11769856217136662085 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R7S7 :
    OAI.Laughlin.Certificate.errorRational 9 (3 : Fin 5) (3 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (3 : Fin 5) (3 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R7S7Row0,
    originalYRowSplitD9R7S7Row1,
    originalYRowSplitD9R7S7Row2,
    originalYRowSplitD9R7S7Row3,
    originalYRowSplitD9R7S7Row4,
    originalYRowSplitD9R7S7Row5,
    originalYRowSplitD9R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
