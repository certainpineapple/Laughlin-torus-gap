import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R9S13Row0 :
    OAI.Laughlin.Certificate.yRow 16 9 13
      (OAI.Laughlin.Certificate.rows[0]!) = (2089134642179376792000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S13Row1 :
    OAI.Laughlin.Certificate.yRow 16 9 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-83964472708269678525 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S13Row2 :
    OAI.Laughlin.Certificate.yRow 16 9 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-7393803119655110183025 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S13Row3 :
    OAI.Laughlin.Certificate.yRow 16 9 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-3137098242056836788405675 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S13Row4 :
    OAI.Laughlin.Certificate.yRow 16 9 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((116507790537585297075225 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S13Row5 :
    OAI.Laughlin.Certificate.yRow 16 9 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-5114963781060096921682725 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S13Row6 :
    OAI.Laughlin.Certificate.yRow 16 9 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((5235322519176536711925 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R9S13 :
    OAI.Laughlin.Certificate.errorRational 16 (4 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (4 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 9 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R9S13Row0,
    originalYRowSplitD16R9S13Row1,
    originalYRowSplitD16R9S13Row2,
    originalYRowSplitD16R9S13Row3,
    originalYRowSplitD16R9S13Row4,
    originalYRowSplitD16R9S13Row5,
    originalYRowSplitD16R9S13Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R9S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
