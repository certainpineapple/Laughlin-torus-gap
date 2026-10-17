import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 17 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 17 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((45189278797610171849625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 17 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((499391651112395627210625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 17 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = (45101302769949905729250 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 17 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-197147685035946884937823125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 17 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((2896427100003475450734196875 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 17 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-231755195927632217409694125 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R1S9 :
    OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (4 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (0 : Fin 9) (4 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R1S9Row0,
    originalYRowSplitD17R1S9Row1,
    originalYRowSplitD17R1S9Row2,
    originalYRowSplitD17R1S9Row3,
    originalYRowSplitD17R1S9Row4,
    originalYRowSplitD17R1S9Row5,
    originalYRowSplitD17R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
