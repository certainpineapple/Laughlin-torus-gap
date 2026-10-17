import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R5S13Row0 :
    OAI.Laughlin.Certificate.yRow 15 5 13
      (OAI.Laughlin.Certificate.rows[0]!) = (2372373786085544241000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S13Row1 :
    OAI.Laughlin.Certificate.yRow 15 5 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((4890638996957298209625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S13Row2 :
    OAI.Laughlin.Certificate.yRow 15 5 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((3840486541860188159564625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S13Row3 :
    OAI.Laughlin.Certificate.yRow 15 5 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((2510757240097089842483625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S13Row4 :
    OAI.Laughlin.Certificate.yRow 15 5 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-25048315642716535979935125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S13Row5 :
    OAI.Laughlin.Certificate.yRow 15 5 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((60170699324479386345577875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S13Row6 :
    OAI.Laughlin.Certificate.yRow 15 5 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-459852880789601799625125 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R5S13 :
    OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (2 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 5 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R5S13Row0,
    originalYRowSplitD15R5S13Row1,
    originalYRowSplitD15R5S13Row2,
    originalYRowSplitD15R5S13Row3,
    originalYRowSplitD15R5S13Row4,
    originalYRowSplitD15R5S13Row5,
    originalYRowSplitD15R5S13Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R5S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
