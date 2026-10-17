import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 10 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((397659207384155114055 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 10 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((318888732116473360515 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 10 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((614921404647632096445615 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 10 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((235988444641764012385635 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 10 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-32499286769083293349605 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 10 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((1786568445285891461313975 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 10 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((1613366299182332347695 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R1S7 :
    OAI.Laughlin.Certificate.errorRational 10 (0 : Fin 5) (3 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (0 : Fin 5) (3 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R1S7Row0,
    originalYRowSplitD10R1S7Row1,
    originalYRowSplitD10R1S7Row2,
    originalYRowSplitD10R1S7Row3,
    originalYRowSplitD10R1S7Row4,
    originalYRowSplitD10R1S7Row5,
    originalYRowSplitD10R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
