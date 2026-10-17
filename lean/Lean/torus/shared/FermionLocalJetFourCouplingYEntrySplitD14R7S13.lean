import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R7S13Row0 :
    OAI.Laughlin.Certificate.yRow 14 7 13
      (OAI.Laughlin.Certificate.rows[0]!) = (448143559341912108675 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S13Row1 :
    OAI.Laughlin.Certificate.yRow 14 7 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-973746357750750258675 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S13Row2 :
    OAI.Laughlin.Certificate.yRow 14 7 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-443725092444898108619775 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S13Row3 :
    OAI.Laughlin.Certificate.yRow 14 7 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((493121030922888680587275 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S13Row4 :
    OAI.Laughlin.Certificate.yRow 14 7 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-568552863578187059597025 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S13Row5 :
    OAI.Laughlin.Certificate.yRow 14 7 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-352769534042250775024575 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S13Row6 :
    OAI.Laughlin.Certificate.yRow 14 7 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((1747746500021558311275 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R7S13 :
    OAI.Laughlin.Certificate.errorRational 14 (3 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (3 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 7 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R7S13Row0,
    originalYRowSplitD14R7S13Row1,
    originalYRowSplitD14R7S13Row2,
    originalYRowSplitD14R7S13Row3,
    originalYRowSplitD14R7S13Row4,
    originalYRowSplitD14R7S13Row5,
    originalYRowSplitD14R7S13Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R7S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
