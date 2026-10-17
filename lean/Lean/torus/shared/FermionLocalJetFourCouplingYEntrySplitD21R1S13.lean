import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R1S13Row0 :
    OAI.Laughlin.Certificate.yRow 21 1 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S13Row1 :
    OAI.Laughlin.Certificate.yRow 21 1 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S13Row2 :
    OAI.Laughlin.Certificate.yRow 21 1 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S13Row3 :
    OAI.Laughlin.Certificate.yRow 21 1 13
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S13Row4 :
    OAI.Laughlin.Certificate.yRow 21 1 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-262649179878034088621356875 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S13Row5 :
    OAI.Laughlin.Certificate.yRow 21 1 13
      (OAI.Laughlin.Certificate.rows[5]!) = (79311299245271683349760000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R1S13Row6 :
    OAI.Laughlin.Certificate.yRow 21 1 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-382568498021717918641355625 / 4) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R1S13 :
    OAI.Laughlin.Certificate.errorRational 21 (0 : Fin 11) (6 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (0 : Fin 11) (6 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 1 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R1S13Row0,
    originalYRowSplitD21R1S13Row1,
    originalYRowSplitD21R1S13Row2,
    originalYRowSplitD21R1S13Row3,
    originalYRowSplitD21R1S13Row4,
    originalYRowSplitD21R1S13Row5,
    originalYRowSplitD21R1S13Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R1S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
