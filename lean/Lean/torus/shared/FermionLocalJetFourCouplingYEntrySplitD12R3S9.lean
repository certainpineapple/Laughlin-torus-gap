import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 12 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-169238171728216635975 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 12 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((65497154326084590525 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 12 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-11048312782305142880085 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 12 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-239156738385031699093575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 12 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((136930581203459588009145 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 12 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-130986594048197258495505 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 12 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-393664012050890690865 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R3S9 :
    OAI.Laughlin.Certificate.errorRational 12 (1 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (1 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R3S9Row0,
    originalYRowSplitD12R3S9Row1,
    originalYRowSplitD12R3S9Row2,
    originalYRowSplitD12R3S9Row3,
    originalYRowSplitD12R3S9Row4,
    originalYRowSplitD12R3S9Row5,
    originalYRowSplitD12R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
