import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 7 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((1647590914974091305 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 7 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-1941155336440971141 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 7 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((13696035226878429190755 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 7 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((21555340744289352133005 / 29360128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 7 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((23982864216689624871615 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 7 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((298255256745963536707095 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 7 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-489275399025456543315 / 33554432) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R5S5 :
    OAI.Laughlin.Certificate.errorRational 7 (2 : Fin 4) (2 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (2 : Fin 4) (2 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R5S5Row0,
    originalYRowSplitD7R5S5Row1,
    originalYRowSplitD7R5S5Row2,
    originalYRowSplitD7R5S5Row3,
    originalYRowSplitD7R5S5Row4,
    originalYRowSplitD7R5S5Row5,
    originalYRowSplitD7R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
