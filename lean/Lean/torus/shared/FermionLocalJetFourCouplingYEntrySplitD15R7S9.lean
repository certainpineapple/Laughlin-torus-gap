import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R7S9Row0 :
    OAI.Laughlin.Certificate.yRow 15 7 9
      (OAI.Laughlin.Certificate.rows[0]!) = (238632861606301570275 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S9Row1 :
    OAI.Laughlin.Certificate.yRow 15 7 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((1474730436864282266025 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S9Row2 :
    OAI.Laughlin.Certificate.yRow 15 7 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-3097634886920702003867775 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S9Row3 :
    OAI.Laughlin.Certificate.yRow 15 7 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-341916017128406666030925 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S9Row4 :
    OAI.Laughlin.Certificate.yRow 15 7 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-1573225257272135349989925 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S9Row5 :
    OAI.Laughlin.Certificate.yRow 15 7 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-645325625011357361186325 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S9Row6 :
    OAI.Laughlin.Certificate.yRow 15 7 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-23415079157368048910025 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R7S9 :
    OAI.Laughlin.Certificate.errorRational 15 (3 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (3 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 7 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R7S9Row0,
    originalYRowSplitD15R7S9Row1,
    originalYRowSplitD15R7S9Row2,
    originalYRowSplitD15R7S9Row3,
    originalYRowSplitD15R7S9Row4,
    originalYRowSplitD15R7S9Row5,
    originalYRowSplitD15R7S9Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R7S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
