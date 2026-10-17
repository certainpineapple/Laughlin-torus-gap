import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 16 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-18720482079879916875 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 16 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-8303159075806116608625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 16 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-96599512248854611775625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 16 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((1684011900505775568217875 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 16 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-1948232105984937122744625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 16 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-81792899713524349449185625 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 16 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-91996798138662100674375 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R5S7 :
    OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (3 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (2 : Fin 8) (3 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R5S7Row0,
    originalYRowSplitD16R5S7Row1,
    originalYRowSplitD16R5S7Row2,
    originalYRowSplitD16R5S7Row3,
    originalYRowSplitD16R5S7Row4,
    originalYRowSplitD16R5S7Row5,
    originalYRowSplitD16R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
