import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 9 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((6601780371974724405 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 9 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((80425013021765873469 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 9 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-335790663177832501263435 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 9 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-99831004317047722319685 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 9 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-8182217896830087939675 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 9 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((4525524576166383102285 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 9 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((4718288145955830089805 / 1048576) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R1S9 :
    OAI.Laughlin.Certificate.errorRational 9 (0 : Fin 5) (4 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (0 : Fin 5) (4 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R1S9Row0,
    originalYRowSplitD9R1S9Row1,
    originalYRowSplitD9R1S9Row2,
    originalYRowSplitD9R1S9Row3,
    originalYRowSplitD9R1S9Row4,
    originalYRowSplitD9R1S9Row5,
    originalYRowSplitD9R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
