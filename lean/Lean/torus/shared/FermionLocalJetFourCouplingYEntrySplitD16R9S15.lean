import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R9S15Row0 :
    OAI.Laughlin.Certificate.yRow 16 9 15
      (OAI.Laughlin.Certificate.rows[0]!) = (8395583521352785758000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S15Row1 :
    OAI.Laughlin.Certificate.yRow 16 9 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((2783560378805982901125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S15Row2 :
    OAI.Laughlin.Certificate.yRow 16 9 15
      (OAI.Laughlin.Certificate.rows[2]!) = (20372863261409051518125 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S15Row3 :
    OAI.Laughlin.Certificate.yRow 16 9 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((-5383199546077381471067625 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S15Row4 :
    OAI.Laughlin.Certificate.yRow 16 9 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-686259666939640735816875 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S15Row5 :
    OAI.Laughlin.Certificate.yRow 16 9 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((-11911522106914824041022375 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R9S15Row6 :
    OAI.Laughlin.Certificate.yRow 16 9 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-13658962761241819646625 / 16) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R9S15 :
    OAI.Laughlin.Certificate.errorRational 16 (4 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (4 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 9 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R9S15Row0,
    originalYRowSplitD16R9S15Row1,
    originalYRowSplitD16R9S15Row2,
    originalYRowSplitD16R9S15Row3,
    originalYRowSplitD16R9S15Row4,
    originalYRowSplitD16R9S15Row5,
    originalYRowSplitD16R9S15Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R9S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
