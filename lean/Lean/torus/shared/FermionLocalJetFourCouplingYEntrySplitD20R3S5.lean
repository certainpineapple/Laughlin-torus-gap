import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 20 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 20 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 20 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 20 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 20 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2601414216110213946532715625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 20 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-23582166720264823102306875 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 20 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((1101383253303246671773640625 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R3S5 :
    OAI.Laughlin.Certificate.errorRational 20 (1 : Fin 10) (2 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (1 : Fin 10) (2 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R3S5Row0,
    originalYRowSplitD20R3S5Row1,
    originalYRowSplitD20R3S5Row2,
    originalYRowSplitD20R3S5Row3,
    originalYRowSplitD20R3S5Row4,
    originalYRowSplitD20R3S5Row5,
    originalYRowSplitD20R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
