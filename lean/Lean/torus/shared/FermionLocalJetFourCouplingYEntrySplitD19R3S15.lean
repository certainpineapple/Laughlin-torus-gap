import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R3S15Row0 :
    OAI.Laughlin.Certificate.yRow 19 3 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S15Row1 :
    OAI.Laughlin.Certificate.yRow 19 3 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S15Row2 :
    OAI.Laughlin.Certificate.yRow 19 3 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S15Row3 :
    OAI.Laughlin.Certificate.yRow 19 3 15
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S15Row4 :
    OAI.Laughlin.Certificate.yRow 19 3 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((856815174968029669773005625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S15Row5 :
    OAI.Laughlin.Certificate.yRow 19 3 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((925178429264895240936125625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S15Row6 :
    OAI.Laughlin.Certificate.yRow 19 3 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((2591283794698650619693125 / 16) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R3S15 :
    OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (7 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (1 : Fin 10) (7 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 3 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R3S15Row0,
    originalYRowSplitD19R3S15Row1,
    originalYRowSplitD19R3S15Row2,
    originalYRowSplitD19R3S15Row3,
    originalYRowSplitD19R3S15Row4,
    originalYRowSplitD19R3S15Row5,
    originalYRowSplitD19R3S15Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R3S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
