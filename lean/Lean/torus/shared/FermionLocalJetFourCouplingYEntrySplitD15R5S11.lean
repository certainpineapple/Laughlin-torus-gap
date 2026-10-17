import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R5S11Row0 :
    OAI.Laughlin.Certificate.yRow 15 5 11
      (OAI.Laughlin.Certificate.rows[0]!) = (-223461965723224016250 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S11Row1 :
    OAI.Laughlin.Certificate.yRow 15 5 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((198497136948016685625 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S11Row2 :
    OAI.Laughlin.Certificate.yRow 15 5 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((1720589467070812972874625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S11Row3 :
    OAI.Laughlin.Certificate.yRow 15 5 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-467850341103831961939125 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S11Row4 :
    OAI.Laughlin.Certificate.yRow 15 5 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2340338730489574098037875 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S11Row5 :
    OAI.Laughlin.Certificate.yRow 15 5 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-12380510107929985540732125 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S11Row6 :
    OAI.Laughlin.Certificate.yRow 15 5 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((10519293076010953801875 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R5S11 :
    OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (2 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 5 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R5S11Row0,
    originalYRowSplitD15R5S11Row1,
    originalYRowSplitD15R5S11Row2,
    originalYRowSplitD15R5S11Row3,
    originalYRowSplitD15R5S11Row4,
    originalYRowSplitD15R5S11Row5,
    originalYRowSplitD15R5S11Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R5S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
