import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 18 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 18 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 18 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 18 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((-3118260882013355604400875 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 18 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-1019972213928793944989044875 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 18 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((1468620885281822715407839875 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 18 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-5426942786181071259229125 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R3S9 :
    OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (4 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (1 : Fin 9) (4 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R3S9Row0,
    originalYRowSplitD18R3S9Row1,
    originalYRowSplitD18R3S9Row2,
    originalYRowSplitD18R3S9Row3,
    originalYRowSplitD18R3S9Row4,
    originalYRowSplitD18R3S9Row5,
    originalYRowSplitD18R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
