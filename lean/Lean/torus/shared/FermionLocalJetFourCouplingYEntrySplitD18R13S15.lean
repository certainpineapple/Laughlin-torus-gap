import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R13S15Row0 :
    OAI.Laughlin.Certificate.yRow 18 13 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S15Row1 :
    OAI.Laughlin.Certificate.yRow 18 13 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S15Row2 :
    OAI.Laughlin.Certificate.yRow 18 13 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S15Row3 :
    OAI.Laughlin.Certificate.yRow 18 13 15
      (OAI.Laughlin.Certificate.rows[3]!) = (95202135040111953603750 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S15Row4 :
    OAI.Laughlin.Certificate.yRow 18 13 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((109550266414439052076875 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S15Row5 :
    OAI.Laughlin.Certificate.yRow 18 13 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((23323908002983726378865625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S15Row6 :
    OAI.Laughlin.Certificate.yRow 18 13 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R13S15 :
    OAI.Laughlin.Certificate.errorRational 18 (6 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (6 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 13 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R13S15Row0,
    originalYRowSplitD18R13S15Row1,
    originalYRowSplitD18R13S15Row2,
    originalYRowSplitD18R13S15Row3,
    originalYRowSplitD18R13S15Row4,
    originalYRowSplitD18R13S15Row5,
    originalYRowSplitD18R13S15Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R13S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
