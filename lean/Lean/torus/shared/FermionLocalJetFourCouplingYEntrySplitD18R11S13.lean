import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R11S13Row0 :
    OAI.Laughlin.Certificate.yRow 18 11 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S13Row1 :
    OAI.Laughlin.Certificate.yRow 18 11 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S13Row2 :
    OAI.Laughlin.Certificate.yRow 18 11 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S13Row3 :
    OAI.Laughlin.Certificate.yRow 18 11 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-68546945745040082945625 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S13Row4 :
    OAI.Laughlin.Certificate.yRow 18 11 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((12230806725209780332750125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S13Row5 :
    OAI.Laughlin.Certificate.yRow 18 11 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-16830289725019549508354625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S13Row6 :
    OAI.Laughlin.Certificate.yRow 18 11 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-336713942383201230222375 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R11S13 :
    OAI.Laughlin.Certificate.errorRational 18 (5 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (5 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 11 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R11S13Row0,
    originalYRowSplitD18R11S13Row1,
    originalYRowSplitD18R11S13Row2,
    originalYRowSplitD18R11S13Row3,
    originalYRowSplitD18R11S13Row4,
    originalYRowSplitD18R11S13Row5,
    originalYRowSplitD18R11S13Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R11S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
