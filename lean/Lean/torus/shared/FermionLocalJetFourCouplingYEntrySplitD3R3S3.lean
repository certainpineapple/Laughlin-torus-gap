import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD3R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 3 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((2634471478568880657 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 3 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((26296293111063980717 / 4697620480) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 3 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((45664206627047238034249 / 3758096384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 3 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((6732493004346615199437 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 3 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((12772753224818271331277 / 3758096384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 3 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((46680757914694576599231 / 15032385536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD3R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 3 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-67233338975498988993 / 67108864) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD3R3S3 :
    OAI.Laughlin.Certificate.errorRational 3 (1 : Fin 2) (1 : Fin 2) =
      TorusLean.FermionM3.errorTable03 (1 : Fin 2) (1 : Fin 2) := by
  change OAI.Laughlin.Certificate.Y 3 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD3R3S3Row0,
    originalYRowSplitD3R3S3Row1,
    originalYRowSplitD3R3S3Row2,
    originalYRowSplitD3R3S3Row3,
    originalYRowSplitD3R3S3Row4,
    originalYRowSplitD3R3S3Row5,
    originalYRowSplitD3R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable03]

#print axioms originalYEntrySplitD3R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
