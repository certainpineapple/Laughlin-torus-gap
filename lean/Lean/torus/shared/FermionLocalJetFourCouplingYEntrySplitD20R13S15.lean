import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R13S15Row0 :
    OAI.Laughlin.Certificate.yRow 20 13 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S15Row1 :
    OAI.Laughlin.Certificate.yRow 20 13 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S15Row2 :
    OAI.Laughlin.Certificate.yRow 20 13 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S15Row3 :
    OAI.Laughlin.Certificate.yRow 20 13 15
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S15Row4 :
    OAI.Laughlin.Certificate.yRow 20 13 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((797709523102574541834375 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S15Row5 :
    OAI.Laughlin.Certificate.yRow 20 13 15
      (OAI.Laughlin.Certificate.rows[5]!) = (-2547339042304777380660000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S15Row6 :
    OAI.Laughlin.Certificate.yRow 20 13 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R13S15 :
    OAI.Laughlin.Certificate.errorRational 20 (6 : Fin 10) (7 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (6 : Fin 10) (7 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 13 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R13S15Row0,
    originalYRowSplitD20R13S15Row1,
    originalYRowSplitD20R13S15Row2,
    originalYRowSplitD20R13S15Row3,
    originalYRowSplitD20R13S15Row4,
    originalYRowSplitD20R13S15Row5,
    originalYRowSplitD20R13S15Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R13S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
