import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 20 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 20 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 20 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 20 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 20 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((613073708803627946634375 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 20 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = (1128926804679472837500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 20 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-3673099908881299778371875 / 32) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R9S9 :
    OAI.Laughlin.Certificate.errorRational 20 (4 : Fin 10) (4 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (4 : Fin 10) (4 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R9S9Row0,
    originalYRowSplitD20R9S9Row1,
    originalYRowSplitD20R9S9Row2,
    originalYRowSplitD20R9S9Row3,
    originalYRowSplitD20R9S9Row4,
    originalYRowSplitD20R9S9Row5,
    originalYRowSplitD20R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
