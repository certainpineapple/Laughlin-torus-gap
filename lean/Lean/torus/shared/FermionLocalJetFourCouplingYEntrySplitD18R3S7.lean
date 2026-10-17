import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 18 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 18 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 18 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 18 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-29087680966706187762811875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 18 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((7483240201636372302615110625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 18 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-5719781695693541893991949375 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 18 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((510184947770501158111831875 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R3S7 :
    OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (3 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (1 : Fin 9) (3 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R3S7Row0,
    originalYRowSplitD18R3S7Row1,
    originalYRowSplitD18R3S7Row2,
    originalYRowSplitD18R3S7Row3,
    originalYRowSplitD18R3S7Row4,
    originalYRowSplitD18R3S7Row5,
    originalYRowSplitD18R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
