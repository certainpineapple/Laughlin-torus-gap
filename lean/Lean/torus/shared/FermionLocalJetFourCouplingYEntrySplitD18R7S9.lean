import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R7S9Row0 :
    OAI.Laughlin.Certificate.yRow 18 7 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S9Row1 :
    OAI.Laughlin.Certificate.yRow 18 7 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S9Row2 :
    OAI.Laughlin.Certificate.yRow 18 7 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S9Row3 :
    OAI.Laughlin.Certificate.yRow 18 7 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((57755674631881018571625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S9Row4 :
    OAI.Laughlin.Certificate.yRow 18 7 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-36929963804142548875168125 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S9Row5 :
    OAI.Laughlin.Certificate.yRow 18 7 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((171200518928034091731860625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S9Row6 :
    OAI.Laughlin.Certificate.yRow 18 7 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((732313837042274793103875 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R7S9 :
    OAI.Laughlin.Certificate.errorRational 18 (3 : Fin 9) (4 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (3 : Fin 9) (4 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 7 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R7S9Row0,
    originalYRowSplitD18R7S9Row1,
    originalYRowSplitD18R7S9Row2,
    originalYRowSplitD18R7S9Row3,
    originalYRowSplitD18R7S9Row4,
    originalYRowSplitD18R7S9Row5,
    originalYRowSplitD18R7S9Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R7S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
