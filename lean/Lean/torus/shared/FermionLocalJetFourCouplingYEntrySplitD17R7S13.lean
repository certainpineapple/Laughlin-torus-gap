import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R7S13Row0 :
    OAI.Laughlin.Certificate.yRow 17 7 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S13Row1 :
    OAI.Laughlin.Certificate.yRow 17 7 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-160161728031378698625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S13Row2 :
    OAI.Laughlin.Certificate.yRow 17 7 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((785399078403326889376875 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S13Row3 :
    OAI.Laughlin.Certificate.yRow 17 7 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((328408770441672875579625 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S13Row4 :
    OAI.Laughlin.Certificate.yRow 17 7 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-12966242020871396606724375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S13Row5 :
    OAI.Laughlin.Certificate.yRow 17 7 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-9076862451856171255408125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S13Row6 :
    OAI.Laughlin.Certificate.yRow 17 7 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-9286257309206617364625 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R7S13 :
    OAI.Laughlin.Certificate.errorRational 17 (3 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (3 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 7 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R7S13Row0,
    originalYRowSplitD17R7S13Row1,
    originalYRowSplitD17R7S13Row2,
    originalYRowSplitD17R7S13Row3,
    originalYRowSplitD17R7S13Row4,
    originalYRowSplitD17R7S13Row5,
    originalYRowSplitD17R7S13Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R7S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
