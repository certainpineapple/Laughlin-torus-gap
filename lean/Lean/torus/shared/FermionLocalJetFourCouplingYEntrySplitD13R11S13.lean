import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R11S13Row0 :
    OAI.Laughlin.Certificate.yRow 13 11 13
      (OAI.Laughlin.Certificate.rows[0]!) = (395078868020226089700 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S13Row1 :
    OAI.Laughlin.Certificate.yRow 13 11 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-859030202996793860175 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S13Row2 :
    OAI.Laughlin.Certificate.yRow 13 11 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-2837244011657113946519775 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S13Row3 :
    OAI.Laughlin.Certificate.yRow 13 11 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((337165831381484157077025 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S13Row4 :
    OAI.Laughlin.Certificate.yRow 13 11 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((134906941002246873592275 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S13Row5 :
    OAI.Laughlin.Certificate.yRow 13 11 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2095640502329133455199075 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R11S13Row6 :
    OAI.Laughlin.Certificate.yRow 13 11 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((20711980163275757831475 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R11S13 :
    OAI.Laughlin.Certificate.errorRational 13 (5 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (5 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 11 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R11S13Row0,
    originalYRowSplitD13R11S13Row1,
    originalYRowSplitD13R11S13Row2,
    originalYRowSplitD13R11S13Row3,
    originalYRowSplitD13R11S13Row4,
    originalYRowSplitD13R11S13Row5,
    originalYRowSplitD13R11S13Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R11S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
