import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R9S13Row0 :
    OAI.Laughlin.Certificate.yRow 18 9 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S13Row1 :
    OAI.Laughlin.Certificate.yRow 18 9 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S13Row2 :
    OAI.Laughlin.Certificate.yRow 18 9 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S13Row3 :
    OAI.Laughlin.Certificate.yRow 18 9 13
      (OAI.Laughlin.Certificate.rows[3]!) = (10740347253943823265750 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S13Row4 :
    OAI.Laughlin.Certificate.yRow 18 9 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-12668256867982322940708375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S13Row5 :
    OAI.Laughlin.Certificate.yRow 18 9 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((37286805192116437794461625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S13Row6 :
    OAI.Laughlin.Certificate.yRow 18 9 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((142120651602260354648625 / 32) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R9S13 :
    OAI.Laughlin.Certificate.errorRational 18 (4 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (4 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 9 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R9S13Row0,
    originalYRowSplitD18R9S13Row1,
    originalYRowSplitD18R9S13Row2,
    originalYRowSplitD18R9S13Row3,
    originalYRowSplitD18R9S13Row4,
    originalYRowSplitD18R9S13Row5,
    originalYRowSplitD18R9S13Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R9S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
