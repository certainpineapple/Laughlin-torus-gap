import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 17 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 17 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((69879962796370076975625 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 17 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-27210865375097735377921875 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 17 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-399040163342206316555625 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 17 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3740276716354083753973125 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 17 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-3416309977477355520814877625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 17 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-29435384720468059107649875 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R1S11 :
    OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (0 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R1S11Row0,
    originalYRowSplitD17R1S11Row1,
    originalYRowSplitD17R1S11Row2,
    originalYRowSplitD17R1S11Row3,
    originalYRowSplitD17R1S11Row4,
    originalYRowSplitD17R1S11Row5,
    originalYRowSplitD17R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
