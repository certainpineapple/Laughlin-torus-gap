import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R11S13Row0 :
    OAI.Laughlin.Certificate.yRow 14 11 13
      (OAI.Laughlin.Certificate.rows[0]!) = (523474874816393600100 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S13Row1 :
    OAI.Laughlin.Certificate.yRow 14 11 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((171432678325300917525 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S13Row2 :
    OAI.Laughlin.Certificate.yRow 14 11 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((639301975278621496466625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S13Row3 :
    OAI.Laughlin.Certificate.yRow 14 11 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-307521383724104518393425 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S13Row4 :
    OAI.Laughlin.Certificate.yRow 14 11 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((2198582544205269919157175 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S13Row5 :
    OAI.Laughlin.Certificate.yRow 14 11 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1382410006534056886117875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R11S13Row6 :
    OAI.Laughlin.Certificate.yRow 14 11 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((14014659196289753226225 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R11S13 :
    OAI.Laughlin.Certificate.errorRational 14 (5 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (5 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 11 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R11S13Row0,
    originalYRowSplitD14R11S13Row1,
    originalYRowSplitD14R11S13Row2,
    originalYRowSplitD14R11S13Row3,
    originalYRowSplitD14R11S13Row4,
    originalYRowSplitD14R11S13Row5,
    originalYRowSplitD14R11S13Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R11S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
