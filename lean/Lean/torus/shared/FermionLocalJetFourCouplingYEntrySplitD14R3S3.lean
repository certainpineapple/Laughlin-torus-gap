import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 14 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((13104742390499846896425 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 14 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((66511187856623417101425 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 14 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((11057493070250831884489425 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 14 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((-16855676140116853729109475 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 14 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((72009059581154573358765075 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 14 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-61434166052039949793352475 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 14 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-16381231927752987236801475 / 1048576) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R3S3 :
    OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (1 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (1 : Fin 7) (1 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R3S3Row0,
    originalYRowSplitD14R3S3Row1,
    originalYRowSplitD14R3S3Row2,
    originalYRowSplitD14R3S3Row3,
    originalYRowSplitD14R3S3Row4,
    originalYRowSplitD14R3S3Row5,
    originalYRowSplitD14R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
