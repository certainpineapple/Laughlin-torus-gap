import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R11S15Row0 :
    OAI.Laughlin.Certificate.yRow 15 11 15
      (OAI.Laughlin.Certificate.rows[0]!) = (-26345501124617989314000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S15Row1 :
    OAI.Laughlin.Certificate.yRow 15 11 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((6964050845120700956625 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S15Row2 :
    OAI.Laughlin.Certificate.yRow 15 11 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((20467079734914905143676625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S15Row3 :
    OAI.Laughlin.Certificate.yRow 15 11 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((101550127621226081923125 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S15Row4 :
    OAI.Laughlin.Certificate.yRow 15 11 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((4654521754951503748438125 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S15Row5 :
    OAI.Laughlin.Certificate.yRow 15 11 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((42335012229403907477338875 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S15Row6 :
    OAI.Laughlin.Certificate.yRow 15 11 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-29445552543915020638125 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R11S15 :
    OAI.Laughlin.Certificate.errorRational 15 (5 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (5 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 11 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R11S15Row0,
    originalYRowSplitD15R11S15Row1,
    originalYRowSplitD15R11S15Row2,
    originalYRowSplitD15R11S15Row3,
    originalYRowSplitD15R11S15Row4,
    originalYRowSplitD15R11S15Row5,
    originalYRowSplitD15R11S15Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R11S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
