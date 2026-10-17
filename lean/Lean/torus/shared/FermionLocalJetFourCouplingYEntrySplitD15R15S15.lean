import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R15S15Row0 :
    OAI.Laughlin.Certificate.yRow 15 15 15
      (OAI.Laughlin.Certificate.rows[0]!) = (87843171603385958760000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R15S15Row1 :
    OAI.Laughlin.Certificate.yRow 15 15 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((17394501358224135770625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R15S15Row2 :
    OAI.Laughlin.Certificate.yRow 15 15 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((1111863284651596654733180625 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R15S15Row3 :
    OAI.Laughlin.Certificate.yRow 15 15 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((25741919932767075878465625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R15S15Row4 :
    OAI.Laughlin.Certificate.yRow 15 15 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((6336174791318863158793125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R15S15Row5 :
    OAI.Laughlin.Certificate.yRow 15 15 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((60274505614590361232263125 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R15S15Row6 :
    OAI.Laughlin.Certificate.yRow 15 15 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R15S15 :
    OAI.Laughlin.Certificate.errorRational 15 (7 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (7 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 15 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R15S15Row0,
    originalYRowSplitD15R15S15Row1,
    originalYRowSplitD15R15S15Row2,
    originalYRowSplitD15R15S15Row3,
    originalYRowSplitD15R15S15Row4,
    originalYRowSplitD15R15S15Row5,
    originalYRowSplitD15R15S15Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R15S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
