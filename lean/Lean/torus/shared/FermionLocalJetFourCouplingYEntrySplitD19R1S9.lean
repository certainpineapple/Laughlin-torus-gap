import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 19 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 19 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 19 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 19 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 19 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((16898385719676739916064301875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 19 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-90158000352705334256435353125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 19 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((3251115558514813756258366875 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R1S9 :
    OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (4 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (0 : Fin 10) (4 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R1S9Row0,
    originalYRowSplitD19R1S9Row1,
    originalYRowSplitD19R1S9Row2,
    originalYRowSplitD19R1S9Row3,
    originalYRowSplitD19R1S9Row4,
    originalYRowSplitD19R1S9Row5,
    originalYRowSplitD19R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
