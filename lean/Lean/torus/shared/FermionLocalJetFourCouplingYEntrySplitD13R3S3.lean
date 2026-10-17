import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R3S3Row0 :
    OAI.Laughlin.Certificate.yRow 13 3 3
      (OAI.Laughlin.Certificate.rows[0]!) = ((2441972282067829005075 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S3Row1 :
    OAI.Laughlin.Certificate.yRow 13 3 3
      (OAI.Laughlin.Certificate.rows[1]!) = ((10600941716872532410725 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S3Row2 :
    OAI.Laughlin.Certificate.yRow 13 3 3
      (OAI.Laughlin.Certificate.rows[2]!) = ((16011491935273756103894625 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S3Row3 :
    OAI.Laughlin.Certificate.yRow 13 3 3
      (OAI.Laughlin.Certificate.rows[3]!) = ((15008538897042682310775 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S3Row4 :
    OAI.Laughlin.Certificate.yRow 13 3 3
      (OAI.Laughlin.Certificate.rows[4]!) = ((-4198284051895701535713075 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S3Row5 :
    OAI.Laughlin.Certificate.yRow 13 3 3
      (OAI.Laughlin.Certificate.rows[5]!) = ((-10535447171675772926923725 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R3S3Row6 :
    OAI.Laughlin.Certificate.yRow 13 3 3
      (OAI.Laughlin.Certificate.rows[6]!) = ((-568138240156920666891525 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R3S3 :
    OAI.Laughlin.Certificate.errorRational 13 (1 : Fin 7) (1 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (1 : Fin 7) (1 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 3 3 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R3S3Row0,
    originalYRowSplitD13R3S3Row1,
    originalYRowSplitD13R3S3Row2,
    originalYRowSplitD13R3S3Row3,
    originalYRowSplitD13R3S3Row4,
    originalYRowSplitD13R3S3Row5,
    originalYRowSplitD13R3S3Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R3S3
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
