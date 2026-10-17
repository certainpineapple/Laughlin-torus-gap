import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 9 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-4083848735613087735 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 9 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((10850262773111775189 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 9 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((151761076607764038274245 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 9 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((32213646099666222250005 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 9 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-19325039457118938251985 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 9 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-457529480254848109995 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 9 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((98390582511496356375 / 1048576) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R3S9 :
    OAI.Laughlin.Certificate.errorRational 9 (1 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (1 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R3S9Row0,
    originalYRowSplitD9R3S9Row1,
    originalYRowSplitD9R3S9Row2,
    originalYRowSplitD9R3S9Row3,
    originalYRowSplitD9R3S9Row4,
    originalYRowSplitD9R3S9Row5,
    originalYRowSplitD9R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
