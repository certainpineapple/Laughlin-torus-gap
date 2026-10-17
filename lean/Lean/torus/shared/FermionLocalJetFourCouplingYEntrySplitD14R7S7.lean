import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 14 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((910540363713264476325 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 14 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((268358484915669693825 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 14 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-1114156013113817389587375 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 14 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((420918421948878828521925 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 14 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-296765046581813884741275 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 14 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((2859326750031813083394225 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 14 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-42677792811880799591025 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R7S7 :
    OAI.Laughlin.Certificate.errorRational 14 (3 : Fin 7) (3 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (3 : Fin 7) (3 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R7S7Row0,
    originalYRowSplitD14R7S7Row1,
    originalYRowSplitD14R7S7Row2,
    originalYRowSplitD14R7S7Row3,
    originalYRowSplitD14R7S7Row4,
    originalYRowSplitD14R7S7Row5,
    originalYRowSplitD14R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
