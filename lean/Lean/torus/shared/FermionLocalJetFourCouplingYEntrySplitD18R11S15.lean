import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R11S15Row0 :
    OAI.Laughlin.Certificate.yRow 18 11 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S15Row1 :
    OAI.Laughlin.Certificate.yRow 18 11 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S15Row2 :
    OAI.Laughlin.Certificate.yRow 18 11 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S15Row3 :
    OAI.Laughlin.Certificate.yRow 18 11 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((-700529059983177612061875 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S15Row4 :
    OAI.Laughlin.Certificate.yRow 18 11 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2672508123256099216213125 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S15Row5 :
    OAI.Laughlin.Certificate.yRow 18 11 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-40154125899741851311689375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S15Row6 :
    OAI.Laughlin.Certificate.yRow 18 11 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-354109354523914356241875 / 32) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R11S15 :
    OAI.Laughlin.Certificate.errorRational 18 (5 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (5 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 11 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R11S15Row0,
    originalYRowSplitD18R11S15Row1,
    originalYRowSplitD18R11S15Row2,
    originalYRowSplitD18R11S15Row3,
    originalYRowSplitD18R11S15Row4,
    originalYRowSplitD18R11S15Row5,
    originalYRowSplitD18R11S15Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R11S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
