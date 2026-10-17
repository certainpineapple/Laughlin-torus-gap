import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R5S11Row0 :
    OAI.Laughlin.Certificate.yRow 19 5 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S11Row1 :
    OAI.Laughlin.Certificate.yRow 19 5 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S11Row2 :
    OAI.Laughlin.Certificate.yRow 19 5 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S11Row3 :
    OAI.Laughlin.Certificate.yRow 19 5 11
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S11Row4 :
    OAI.Laughlin.Certificate.yRow 19 5 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-241000996897930184227186875 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S11Row5 :
    OAI.Laughlin.Certificate.yRow 19 5 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((1394926502084200922614903125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S11Row6 :
    OAI.Laughlin.Certificate.yRow 19 5 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-45997842406725620943406875 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R5S11 :
    OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (5 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (2 : Fin 10) (5 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 5 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R5S11Row0,
    originalYRowSplitD19R5S11Row1,
    originalYRowSplitD19R5S11Row2,
    originalYRowSplitD19R5S11Row3,
    originalYRowSplitD19R5S11Row4,
    originalYRowSplitD19R5S11Row5,
    originalYRowSplitD19R5S11Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R5S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
