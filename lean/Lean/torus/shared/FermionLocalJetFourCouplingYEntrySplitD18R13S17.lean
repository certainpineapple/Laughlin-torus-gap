import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R13S17Row0 :
    OAI.Laughlin.Certificate.yRow 18 13 17
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S17Row1 :
    OAI.Laughlin.Certificate.yRow 18 13 17
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S17Row2 :
    OAI.Laughlin.Certificate.yRow 18 13 17
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S17Row3 :
    OAI.Laughlin.Certificate.yRow 18 13 17
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S17Row4 :
    OAI.Laughlin.Certificate.yRow 18 13 17
      (OAI.Laughlin.Certificate.rows[4]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S17Row5 :
    OAI.Laughlin.Certificate.yRow 18 13 17
      (OAI.Laughlin.Certificate.rows[5]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R13S17Row6 :
    OAI.Laughlin.Certificate.yRow 18 13 17
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R13S17 :
    OAI.Laughlin.Certificate.errorRational 18 (6 : Fin 9) (8 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (6 : Fin 9) (8 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 13 17 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R13S17Row0,
    originalYRowSplitD18R13S17Row1,
    originalYRowSplitD18R13S17Row2,
    originalYRowSplitD18R13S17Row3,
    originalYRowSplitD18R13S17Row4,
    originalYRowSplitD18R13S17Row5,
    originalYRowSplitD18R13S17Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R13S17
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
