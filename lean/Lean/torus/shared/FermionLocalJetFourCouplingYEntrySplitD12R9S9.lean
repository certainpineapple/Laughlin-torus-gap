import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 12 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((13151311742009981925 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 12 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((72553110821681166135 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 12 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-95947584889136943022245 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 12 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-14906023997839947911925 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 12 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2579245600783411356615 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 12 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((41556951079445302403085 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 12 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-961138132032291306975 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R9S9 :
    OAI.Laughlin.Certificate.errorRational 12 (4 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (4 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R9S9Row0,
    originalYRowSplitD12R9S9Row1,
    originalYRowSplitD12R9S9Row2,
    originalYRowSplitD12R9S9Row3,
    originalYRowSplitD12R9S9Row4,
    originalYRowSplitD12R9S9Row5,
    originalYRowSplitD12R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
