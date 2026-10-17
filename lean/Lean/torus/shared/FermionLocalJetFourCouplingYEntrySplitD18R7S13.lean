import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R7S13Row0 :
    OAI.Laughlin.Certificate.yRow 18 7 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S13Row1 :
    OAI.Laughlin.Certificate.yRow 18 7 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S13Row2 :
    OAI.Laughlin.Certificate.yRow 18 7 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S13Row3 :
    OAI.Laughlin.Certificate.yRow 18 7 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((50093915521372779931875 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S13Row4 :
    OAI.Laughlin.Certificate.yRow 18 7 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((23345645194689073307926875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S13Row5 :
    OAI.Laughlin.Certificate.yRow 18 7 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-131725420774380086874845625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S13Row6 :
    OAI.Laughlin.Certificate.yRow 18 7 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-847989636431897553969375 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R7S13 :
    OAI.Laughlin.Certificate.errorRational 18 (3 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (3 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 7 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R7S13Row0,
    originalYRowSplitD18R7S13Row1,
    originalYRowSplitD18R7S13Row2,
    originalYRowSplitD18R7S13Row3,
    originalYRowSplitD18R7S13Row4,
    originalYRowSplitD18R7S13Row5,
    originalYRowSplitD18R7S13Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R7S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
