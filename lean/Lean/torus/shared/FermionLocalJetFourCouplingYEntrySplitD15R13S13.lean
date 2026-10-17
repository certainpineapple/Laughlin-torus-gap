import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R13S13Row0 :
    OAI.Laughlin.Certificate.yRow 15 13 13
      (OAI.Laughlin.Certificate.rows[0]!) = (12829883559770723846400 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S13Row1 :
    OAI.Laughlin.Certificate.yRow 15 13 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-803896096601200177575 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S13Row2 :
    OAI.Laughlin.Certificate.yRow 15 13 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((1332814308298698217417425 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S13Row3 :
    OAI.Laughlin.Certificate.yRow 15 13 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((2637339532564465500797025 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S13Row4 :
    OAI.Laughlin.Certificate.yRow 15 13 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((26008316077430184596938125 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S13Row5 :
    OAI.Laughlin.Certificate.yRow 15 13 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-63272492865866009373122475 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R13S13Row6 :
    OAI.Laughlin.Certificate.yRow 15 13 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-160702379293040115906375 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R13S13 :
    OAI.Laughlin.Certificate.errorRational 15 (6 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (6 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 13 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R13S13Row0,
    originalYRowSplitD15R13S13Row1,
    originalYRowSplitD15R13S13Row2,
    originalYRowSplitD15R13S13Row3,
    originalYRowSplitD15R13S13Row4,
    originalYRowSplitD15R13S13Row5,
    originalYRowSplitD15R13S13Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R13S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
