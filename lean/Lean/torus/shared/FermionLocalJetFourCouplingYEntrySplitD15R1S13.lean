import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R1S13Row0 :
    OAI.Laughlin.Certificate.yRow 15 1 13
      (OAI.Laughlin.Certificate.rows[0]!) = (10912728269306194305975 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S13Row1 :
    OAI.Laughlin.Certificate.yRow 15 1 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-408241800581105969252775 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S13Row2 :
    OAI.Laughlin.Certificate.yRow 15 1 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-1674452438678467037061046575 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S13Row3 :
    OAI.Laughlin.Certificate.yRow 15 1 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-185245037917075841555725875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S13Row4 :
    OAI.Laughlin.Certificate.yRow 15 1 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-114858699353558865095165775 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S13Row5 :
    OAI.Laughlin.Certificate.yRow 15 1 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-772961988103013073027888225 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S13Row6 :
    OAI.Laughlin.Certificate.yRow 15 1 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((12704219834636626343672625 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R1S13 :
    OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (0 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 1 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R1S13Row0,
    originalYRowSplitD15R1S13Row1,
    originalYRowSplitD15R1S13Row2,
    originalYRowSplitD15R1S13Row3,
    originalYRowSplitD15R1S13Row4,
    originalYRowSplitD15R1S13Row5,
    originalYRowSplitD15R1S13Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R1S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
