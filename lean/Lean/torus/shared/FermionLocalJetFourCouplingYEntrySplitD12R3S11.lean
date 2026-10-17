import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R3S11Row0 :
    OAI.Laughlin.Certificate.yRow 12 3 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-624924655486443132975 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S11Row1 :
    OAI.Laughlin.Certificate.yRow 12 3 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((280303172763223445055 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S11Row2 :
    OAI.Laughlin.Certificate.yRow 12 3 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-95334173938918474874325 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S11Row3 :
    OAI.Laughlin.Certificate.yRow 12 3 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((286902179608012920965475 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S11Row4 :
    OAI.Laughlin.Certificate.yRow 12 3 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((34505963664927349188825 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S11Row5 :
    OAI.Laughlin.Certificate.yRow 12 3 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((60450932010799360356975 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S11Row6 :
    OAI.Laughlin.Certificate.yRow 12 3 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((55863208336323856804875 / 131072) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R3S11 :
    OAI.Laughlin.Certificate.errorRational 12 (1 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (1 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 3 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R3S11Row0,
    originalYRowSplitD12R3S11Row1,
    originalYRowSplitD12R3S11Row2,
    originalYRowSplitD12R3S11Row3,
    originalYRowSplitD12R3S11Row4,
    originalYRowSplitD12R3S11Row5,
    originalYRowSplitD12R3S11Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R3S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
