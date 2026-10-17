import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 19 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 19 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 19 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 19 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 19 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-30115004004807411779363649375 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 19 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((110126807530252217964094460625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 19 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1240473471399506064143548125 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R3S5 :
    OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (2 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (1 : Fin 10) (2 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R3S5Row0,
    originalYRowSplitD19R3S5Row1,
    originalYRowSplitD19R3S5Row2,
    originalYRowSplitD19R3S5Row3,
    originalYRowSplitD19R3S5Row4,
    originalYRowSplitD19R3S5Row5,
    originalYRowSplitD19R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
