import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R9S15Row0 :
    OAI.Laughlin.Certificate.yRow 18 9 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S15Row1 :
    OAI.Laughlin.Certificate.yRow 18 9 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S15Row2 :
    OAI.Laughlin.Certificate.yRow 18 9 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S15Row3 :
    OAI.Laughlin.Certificate.yRow 18 9 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((54881550767289915293625 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S15Row4 :
    OAI.Laughlin.Certificate.yRow 18 9 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-580414914784726235589375 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S15Row5 :
    OAI.Laughlin.Certificate.yRow 18 9 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((26120541696380352325479375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R9S15Row6 :
    OAI.Laughlin.Certificate.yRow 18 9 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((-14205470668016210958375 / 16) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R9S15 :
    OAI.Laughlin.Certificate.errorRational 18 (4 : Fin 9) (7 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (4 : Fin 9) (7 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 9 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R9S15Row0,
    originalYRowSplitD18R9S15Row1,
    originalYRowSplitD18R9S15Row2,
    originalYRowSplitD18R9S15Row3,
    originalYRowSplitD18R9S15Row4,
    originalYRowSplitD18R9S15Row5,
    originalYRowSplitD18R9S15Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R9S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
