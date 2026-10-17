import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R5S15Row0 :
    OAI.Laughlin.Certificate.yRow 18 5 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S15Row1 :
    OAI.Laughlin.Certificate.yRow 18 5 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S15Row2 :
    OAI.Laughlin.Certificate.yRow 18 5 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S15Row3 :
    OAI.Laughlin.Certificate.yRow 18 5 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((-82414358280513916531875 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S15Row4 :
    OAI.Laughlin.Certificate.yRow 18 5 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((1574962553934105983521875 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S15Row5 :
    OAI.Laughlin.Certificate.yRow 18 5 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-254866014806536829811740625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S15Row6 :
    OAI.Laughlin.Certificate.yRow 18 5 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1148376549212685804886875 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R5S15 :
    OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (2 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 5 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R5S15Row0,
    originalYRowSplitD18R5S15Row1,
    originalYRowSplitD18R5S15Row2,
    originalYRowSplitD18R5S15Row3,
    originalYRowSplitD18R5S15Row4,
    originalYRowSplitD18R5S15Row5,
    originalYRowSplitD18R5S15Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R5S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
