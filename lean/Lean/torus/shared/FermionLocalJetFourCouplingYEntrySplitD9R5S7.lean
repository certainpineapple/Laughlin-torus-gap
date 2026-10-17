import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 9 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((419215496975254035 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 9 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-11712343812967273959 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 9 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-12700497512691384839595 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 9 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((1166567238237247684965 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 9 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((845035579081968238185 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 9 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-61240048077972101288805 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 9 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((58020512171994008595 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R5S7 :
    OAI.Laughlin.Certificate.errorRational 9 (2 : Fin 5) (3 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (2 : Fin 5) (3 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R5S7Row0,
    originalYRowSplitD9R5S7Row1,
    originalYRowSplitD9R5S7Row2,
    originalYRowSplitD9R5S7Row3,
    originalYRowSplitD9R5S7Row4,
    originalYRowSplitD9R5S7Row5,
    originalYRowSplitD9R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
