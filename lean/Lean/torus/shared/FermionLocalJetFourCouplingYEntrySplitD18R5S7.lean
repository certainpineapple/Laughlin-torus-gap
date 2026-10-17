import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 18 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 18 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 18 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 18 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-86730363761542768141875 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 18 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-870217083601431055023909375 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 18 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((3849185595222718936400840625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 18 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((39597742229556641023018125 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R5S7 :
    OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (3 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (2 : Fin 9) (3 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R5S7Row0,
    originalYRowSplitD18R5S7Row1,
    originalYRowSplitD18R5S7Row2,
    originalYRowSplitD18R5S7Row3,
    originalYRowSplitD18R5S7Row4,
    originalYRowSplitD18R5S7Row5,
    originalYRowSplitD18R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
