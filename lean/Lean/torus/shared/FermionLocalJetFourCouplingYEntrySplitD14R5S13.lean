import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R5S13Row0 :
    OAI.Laughlin.Certificate.yRow 14 5 13
      (OAI.Laughlin.Certificate.rows[0]!) = (-934488068436876128175 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S13Row1 :
    OAI.Laughlin.Certificate.yRow 14 5 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((152286222425757044625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S13Row2 :
    OAI.Laughlin.Certificate.yRow 14 5 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-5330759246238974907934575 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S13Row3 :
    OAI.Laughlin.Certificate.yRow 14 5 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((1067495937603665577032025 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S13Row4 :
    OAI.Laughlin.Certificate.yRow 14 5 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((5102606947729333011415875 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S13Row5 :
    OAI.Laughlin.Certificate.yRow 14 5 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-8912995777057846476170025 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R5S13Row6 :
    OAI.Laughlin.Certificate.yRow 14 5 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((89105755374753388996725 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R5S13 :
    OAI.Laughlin.Certificate.errorRational 14 (2 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (2 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 5 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R5S13Row0,
    originalYRowSplitD14R5S13Row1,
    originalYRowSplitD14R5S13Row2,
    originalYRowSplitD14R5S13Row3,
    originalYRowSplitD14R5S13Row4,
    originalYRowSplitD14R5S13Row5,
    originalYRowSplitD14R5S13Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R5S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
