import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 19 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 19 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 19 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 19 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 19 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((16344427724002372608534375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 19 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((52720120002574386258159375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 19 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((186529666688183530096875 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R9S9 :
    OAI.Laughlin.Certificate.errorRational 19 (4 : Fin 10) (4 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (4 : Fin 10) (4 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R9S9Row0,
    originalYRowSplitD19R9S9Row1,
    originalYRowSplitD19R9S9Row2,
    originalYRowSplitD19R9S9Row3,
    originalYRowSplitD19R9S9Row4,
    originalYRowSplitD19R9S9Row5,
    originalYRowSplitD19R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
