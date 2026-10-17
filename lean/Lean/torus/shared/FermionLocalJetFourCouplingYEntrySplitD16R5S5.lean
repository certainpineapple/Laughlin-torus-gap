import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 16 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = (3127076185858929005625 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 16 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((17412014178779114750625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 16 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-546347204024308218118125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 16 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((13263562892020261190225625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 16 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((3388121713725589977530625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 16 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((400853043340474977051463125 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 16 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-3992399525341477664308125 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R5S5 :
    OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (2 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (2 : Fin 8) (2 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R5S5Row0,
    originalYRowSplitD16R5S5Row1,
    originalYRowSplitD16R5S5Row2,
    originalYRowSplitD16R5S5Row3,
    originalYRowSplitD16R5S5Row4,
    originalYRowSplitD16R5S5Row5,
    originalYRowSplitD16R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
