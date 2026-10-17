import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 19 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 19 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 19 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 19 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 19 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((674703433780973525137584375 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 19 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1985232736314341658960440625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 19 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((10760554523206426481668125 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R5S9 :
    OAI.Laughlin.Certificate.errorRational 19 (2 : Fin 10) (4 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (2 : Fin 10) (4 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R5S9Row0,
    originalYRowSplitD19R5S9Row1,
    originalYRowSplitD19R5S9Row2,
    originalYRowSplitD19R5S9Row3,
    originalYRowSplitD19R5S9Row4,
    originalYRowSplitD19R5S9Row5,
    originalYRowSplitD19R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
