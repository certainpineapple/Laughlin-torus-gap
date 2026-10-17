import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD3R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 3 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((1307203966987404003 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 3 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((360970776651820864437 / 18790481920) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 3 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((53967947609795693004297 / 15032385536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 3 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((3348699948464935784469 / 3758096384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 3 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((10465558338818236092863 / 15032385536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 3 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((114418693745636093248577 / 180388626432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 3 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-382974676315487577951 / 1073741824) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD3R1S1 :
    OAI.Laughlin.Certificate.errorRational 3 (0 : Fin 2) (0 : Fin 2) =
      TorusLean.FermionM3.errorTable03 (0 : Fin 2) (0 : Fin 2) := by
  change OAI.Laughlin.Certificate.Y 3 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD3R1S1Row0,
    originalYRowSplitD3R1S1Row1,
    originalYRowSplitD3R1S1Row2,
    originalYRowSplitD3R1S1Row3,
    originalYRowSplitD3R1S1Row4,
    originalYRowSplitD3R1S1Row5,
    originalYRowSplitD3R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable03]

#print axioms originalYEntrySplitD3R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
