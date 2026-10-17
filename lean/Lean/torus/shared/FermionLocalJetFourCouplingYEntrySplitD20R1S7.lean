import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 20 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 20 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 20 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 20 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 20 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((1274401002955563777040621875 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 20 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-44371385710705307205826875 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 20 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-135188537902759223652144375 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R1S7 :
    OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (3 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (0 : Fin 10) (3 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R1S7Row0,
    originalYRowSplitD20R1S7Row1,
    originalYRowSplitD20R1S7Row2,
    originalYRowSplitD20R1S7Row3,
    originalYRowSplitD20R1S7Row4,
    originalYRowSplitD20R1S7Row5,
    originalYRowSplitD20R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
