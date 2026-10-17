import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R11S15Row0 :
    OAI.Laughlin.Certificate.yRow 17 11 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S15Row1 :
    OAI.Laughlin.Certificate.yRow 17 11 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((621471251682535629375 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S15Row2 :
    OAI.Laughlin.Certificate.yRow 17 11 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((1088408819660068365834375 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S15Row3 :
    OAI.Laughlin.Certificate.yRow 17 11 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((-595126237617677069679375 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S15Row4 :
    OAI.Laughlin.Certificate.yRow 17 11 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-812340433276158892730625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S15Row5 :
    OAI.Laughlin.Certificate.yRow 17 11 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((17752859889228252235321875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S15Row6 :
    OAI.Laughlin.Certificate.yRow 17 11 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-176927556595801493356875 / 32) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R11S15 :
    OAI.Laughlin.Certificate.errorRational 17 (5 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (5 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 11 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R11S15Row0,
    originalYRowSplitD17R11S15Row1,
    originalYRowSplitD17R11S15Row2,
    originalYRowSplitD17R11S15Row3,
    originalYRowSplitD17R11S15Row4,
    originalYRowSplitD17R11S15Row5,
    originalYRowSplitD17R11S15Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R11S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
