import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R7S11Row0 :
    OAI.Laughlin.Certificate.yRow 17 7 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S11Row1 :
    OAI.Laughlin.Certificate.yRow 17 7 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((215749143863858941875 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S11Row2 :
    OAI.Laughlin.Certificate.yRow 17 7 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-949642856518963685203125 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S11Row3 :
    OAI.Laughlin.Certificate.yRow 17 7 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-860020975242967075374375 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S11Row4 :
    OAI.Laughlin.Certificate.yRow 17 7 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-733379583884725017961875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S11Row5 :
    OAI.Laughlin.Certificate.yRow 17 7 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((29131720895245269287188125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S11Row6 :
    OAI.Laughlin.Certificate.yRow 17 7 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((398945928959637030365625 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R7S11 :
    OAI.Laughlin.Certificate.errorRational 17 (3 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (3 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 7 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R7S11Row0,
    originalYRowSplitD17R7S11Row1,
    originalYRowSplitD17R7S11Row2,
    originalYRowSplitD17R7S11Row3,
    originalYRowSplitD17R7S11Row4,
    originalYRowSplitD17R7S11Row5,
    originalYRowSplitD17R7S11Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R7S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
