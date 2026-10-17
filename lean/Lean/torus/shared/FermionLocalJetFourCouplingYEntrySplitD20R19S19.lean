import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R19S19Row0 :
    OAI.Laughlin.Certificate.yRow 20 19 19
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R19S19Row1 :
    OAI.Laughlin.Certificate.yRow 20 19 19
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R19S19Row2 :
    OAI.Laughlin.Certificate.yRow 20 19 19
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R19S19Row3 :
    OAI.Laughlin.Certificate.yRow 20 19 19
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R19S19Row4 :
    OAI.Laughlin.Certificate.yRow 20 19 19
      (OAI.Laughlin.Certificate.rows[4]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R19S19Row5 :
    OAI.Laughlin.Certificate.yRow 20 19 19
      (OAI.Laughlin.Certificate.rows[5]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R19S19Row6 :
    OAI.Laughlin.Certificate.yRow 20 19 19
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R19S19 :
    OAI.Laughlin.Certificate.errorRational 20 (9 : Fin 10) (9 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (9 : Fin 10) (9 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 19 19 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R19S19Row0,
    originalYRowSplitD20R19S19Row1,
    originalYRowSplitD20R19S19Row2,
    originalYRowSplitD20R19S19Row3,
    originalYRowSplitD20R19S19Row4,
    originalYRowSplitD20R19S19Row5,
    originalYRowSplitD20R19S19Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R19S19
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
