import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R1S13Row0 :
    OAI.Laughlin.Certificate.yRow 16 1 13
      (OAI.Laughlin.Certificate.rows[0]!) = (-176544292540907198407500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S13Row1 :
    OAI.Laughlin.Certificate.yRow 16 1 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-2105049022821132262875 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S13Row2 :
    OAI.Laughlin.Certificate.yRow 16 1 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-5790475847213640477019125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S13Row3 :
    OAI.Laughlin.Certificate.yRow 16 1 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-482764482877292944190737875 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S13Row4 :
    OAI.Laughlin.Certificate.yRow 16 1 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-10941983034624069905602125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S13Row5 :
    OAI.Laughlin.Certificate.yRow 16 1 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((873662281616424367545352875 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S13Row6 :
    OAI.Laughlin.Certificate.yRow 16 1 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-7204766102483708097714375 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R1S13 :
    OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (0 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 1 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R1S13Row0,
    originalYRowSplitD16R1S13Row1,
    originalYRowSplitD16R1S13Row2,
    originalYRowSplitD16R1S13Row3,
    originalYRowSplitD16R1S13Row4,
    originalYRowSplitD16R1S13Row5,
    originalYRowSplitD16R1S13Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R1S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
