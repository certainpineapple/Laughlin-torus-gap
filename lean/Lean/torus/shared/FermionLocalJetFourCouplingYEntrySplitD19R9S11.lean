import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R9S11Row0 :
    OAI.Laughlin.Certificate.yRow 19 9 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S11Row1 :
    OAI.Laughlin.Certificate.yRow 19 9 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S11Row2 :
    OAI.Laughlin.Certificate.yRow 19 9 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S11Row3 :
    OAI.Laughlin.Certificate.yRow 19 9 11
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S11Row4 :
    OAI.Laughlin.Certificate.yRow 19 9 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-11792320610021077549066875 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S11Row5 :
    OAI.Laughlin.Certificate.yRow 19 9 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1870530864397973599696875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S11Row6 :
    OAI.Laughlin.Certificate.yRow 19 9 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1650517477391124650818125 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R9S11 :
    OAI.Laughlin.Certificate.errorRational 19 (4 : Fin 10) (5 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (4 : Fin 10) (5 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 9 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R9S11Row0,
    originalYRowSplitD19R9S11Row1,
    originalYRowSplitD19R9S11Row2,
    originalYRowSplitD19R9S11Row3,
    originalYRowSplitD19R9S11Row4,
    originalYRowSplitD19R9S11Row5,
    originalYRowSplitD19R9S11Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R9S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
