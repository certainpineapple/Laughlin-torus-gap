import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R11S15Row0 :
    OAI.Laughlin.Certificate.yRow 16 11 15
      (OAI.Laughlin.Certificate.rows[0]!) = (5013158388007679910000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S15Row1 :
    OAI.Laughlin.Certificate.yRow 16 11 15
      (OAI.Laughlin.Certificate.rows[1]!) = (-2255321176264406250 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S15Row2 :
    OAI.Laughlin.Certificate.yRow 16 11 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-6694438630719725510625 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S15Row3 :
    OAI.Laughlin.Certificate.yRow 16 11 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((1469729021765317406218125 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S15Row4 :
    OAI.Laughlin.Certificate.yRow 16 11 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((2835597326242061215209375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S15Row5 :
    OAI.Laughlin.Certificate.yRow 16 11 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((24920882592995271283025625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S15Row6 :
    OAI.Laughlin.Certificate.yRow 16 11 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-117866957286430539061875 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R11S15 :
    OAI.Laughlin.Certificate.errorRational 16 (5 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (5 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 11 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R11S15Row0,
    originalYRowSplitD16R11S15Row1,
    originalYRowSplitD16R11S15Row2,
    originalYRowSplitD16R11S15Row3,
    originalYRowSplitD16R11S15Row4,
    originalYRowSplitD16R11S15Row5,
    originalYRowSplitD16R11S15Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R11S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
