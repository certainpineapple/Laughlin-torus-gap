import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 14 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-39172795410228839233875 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 14 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((35607333479607725861025 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 14 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((38761831706234736307633425 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 14 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-615683627683126219792575 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 14 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3415282842968267864875425 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 14 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((52695706960600395345450225 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 14 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-58958909158271472625275 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R1S9 :
    OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (4 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (0 : Fin 7) (4 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R1S9Row0,
    originalYRowSplitD14R1S9Row1,
    originalYRowSplitD14R1S9Row2,
    originalYRowSplitD14R1S9Row3,
    originalYRowSplitD14R1S9Row4,
    originalYRowSplitD14R1S9Row5,
    originalYRowSplitD14R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
