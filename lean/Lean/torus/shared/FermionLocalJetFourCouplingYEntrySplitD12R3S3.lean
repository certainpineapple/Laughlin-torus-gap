import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 12 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((1854757936974239569125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 12 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((-867873763798220361465 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 12 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((2541566727060647448297195 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 12 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((507066830267886637034715 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 12 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-69974324074844458436115 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 12 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((381488801697088900264485 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 12 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-223054274694083676161535 / 2097152) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R3S3 :
    OAI.Laughlin.Certificate.errorRational 12 (1 : Fin 6) (1 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (1 : Fin 6) (1 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R3S3Row0,
    originalYRowSplitD12R3S3Row1,
    originalYRowSplitD12R3S3Row2,
    originalYRowSplitD12R3S3Row3,
    originalYRowSplitD12R3S3Row4,
    originalYRowSplitD12R3S3Row5,
    originalYRowSplitD12R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
