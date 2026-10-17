import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 19 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 19 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 19 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 19 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 19 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-1323270911124208268776929375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 19 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((5944056844563123304814420625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 19 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-76161792417616328234686875 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R3S9 :
    OAI.Laughlin.Certificate.errorRational 19 (1 : Fin 10) (4 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (1 : Fin 10) (4 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R3S9Row0,
    originalYRowSplitD19R3S9Row1,
    originalYRowSplitD19R3S9Row2,
    originalYRowSplitD19R3S9Row3,
    originalYRowSplitD19R3S9Row4,
    originalYRowSplitD19R3S9Row5,
    originalYRowSplitD19R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
