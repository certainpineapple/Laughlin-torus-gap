import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 8 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((76640875416000675 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 8 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((174426263694933807 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 8 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((2761275840379361416995 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 8 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((702428309218164239085 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 8 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((2911950561638159921355 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 8 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((20424443618431088962035 / 58720256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 8 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-74303915387983228845 / 2097152) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R3S5 :
    OAI.Laughlin.Certificate.errorRational 8 (1 : Fin 4) (2 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (1 : Fin 4) (2 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R3S5Row0,
    originalYRowSplitD8R3S5Row1,
    originalYRowSplitD8R3S5Row2,
    originalYRowSplitD8R3S5Row3,
    originalYRowSplitD8R3S5Row4,
    originalYRowSplitD8R3S5Row5,
    originalYRowSplitD8R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
