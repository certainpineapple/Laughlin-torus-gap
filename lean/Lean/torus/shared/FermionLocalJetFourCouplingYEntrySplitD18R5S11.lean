import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R5S11Row0 :
    OAI.Laughlin.Certificate.yRow 18 5 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S11Row1 :
    OAI.Laughlin.Certificate.yRow 18 5 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S11Row2 :
    OAI.Laughlin.Certificate.yRow 18 5 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S11Row3 :
    OAI.Laughlin.Certificate.yRow 18 5 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((118679114565791129975625 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S11Row4 :
    OAI.Laughlin.Certificate.yRow 18 5 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-58223099755406532094273125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S11Row5 :
    OAI.Laughlin.Certificate.yRow 18 5 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((341915613899661437136125625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S11Row6 :
    OAI.Laughlin.Certificate.yRow 18 5 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-13306325104386451116354375 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R5S11 :
    OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (2 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 5 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R5S11Row0,
    originalYRowSplitD18R5S11Row1,
    originalYRowSplitD18R5S11Row2,
    originalYRowSplitD18R5S11Row3,
    originalYRowSplitD18R5S11Row4,
    originalYRowSplitD18R5S11Row5,
    originalYRowSplitD18R5S11Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R5S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
