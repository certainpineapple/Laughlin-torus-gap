import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R11S13Row0 :
    OAI.Laughlin.Certificate.yRow 16 11 13
      (OAI.Laughlin.Certificate.rows[0]!) = (1247460980941014840000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S13Row1 :
    OAI.Laughlin.Certificate.yRow 16 11 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((12424897222708595625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S13Row2 :
    OAI.Laughlin.Certificate.yRow 16 11 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-5192982329512541689125 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S13Row3 :
    OAI.Laughlin.Certificate.yRow 16 11 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1989489040116761821262625 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S13Row4 :
    OAI.Laughlin.Certificate.yRow 16 11 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3500057229191113821033375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S13Row5 :
    OAI.Laughlin.Certificate.yRow 16 11 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1843699741949645920679625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S13Row6 :
    OAI.Laughlin.Certificate.yRow 16 11 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-7860990772850545204875 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R11S13 :
    OAI.Laughlin.Certificate.errorRational 16 (5 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (5 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 11 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R11S13Row0,
    originalYRowSplitD16R11S13Row1,
    originalYRowSplitD16R11S13Row2,
    originalYRowSplitD16R11S13Row3,
    originalYRowSplitD16R11S13Row4,
    originalYRowSplitD16R11S13Row5,
    originalYRowSplitD16R11S13Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R11S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
