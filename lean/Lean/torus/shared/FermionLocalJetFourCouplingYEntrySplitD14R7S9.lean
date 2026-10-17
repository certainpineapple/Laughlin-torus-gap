import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R7S9Row0 :
    OAI.Laughlin.Certificate.yRow 14 7 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-154835992089092788425 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S9Row1 :
    OAI.Laughlin.Certificate.yRow 14 7 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((121198042420702384725 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S9Row2 :
    OAI.Laughlin.Certificate.yRow 14 7 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((586045839613326695100225 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S9Row3 :
    OAI.Laughlin.Certificate.yRow 14 7 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-57526834561766557783425 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S9Row4 :
    OAI.Laughlin.Certificate.yRow 14 7 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((6547970921738681602125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S9Row5 :
    OAI.Laughlin.Certificate.yRow 14 7 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((265879082171548440858375 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S9Row6 :
    OAI.Laughlin.Certificate.yRow 14 7 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2490472507787806495275 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R7S9 :
    OAI.Laughlin.Certificate.errorRational 14 (3 : Fin 7) (4 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (3 : Fin 7) (4 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 7 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R7S9Row0,
    originalYRowSplitD14R7S9Row1,
    originalYRowSplitD14R7S9Row2,
    originalYRowSplitD14R7S9Row3,
    originalYRowSplitD14R7S9Row4,
    originalYRowSplitD14R7S9Row5,
    originalYRowSplitD14R7S9Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R7S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
