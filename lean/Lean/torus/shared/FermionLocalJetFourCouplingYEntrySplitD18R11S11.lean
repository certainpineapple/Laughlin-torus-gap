import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R11S11Row0 :
    OAI.Laughlin.Certificate.yRow 18 11 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S11Row1 :
    OAI.Laughlin.Certificate.yRow 18 11 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S11Row2 :
    OAI.Laughlin.Certificate.yRow 18 11 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S11Row3 :
    OAI.Laughlin.Certificate.yRow 18 11 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((1008782575039072090805625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S11Row4 :
    OAI.Laughlin.Certificate.yRow 18 11 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-4177042068504856628991375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S11Row5 :
    OAI.Laughlin.Certificate.yRow 18 11 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((15491270798019430378531875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R11S11Row6 :
    OAI.Laughlin.Certificate.yRow 18 11 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-889369496982319601296125 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R11S11 :
    OAI.Laughlin.Certificate.errorRational 18 (5 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (5 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 11 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R11S11Row0,
    originalYRowSplitD18R11S11Row1,
    originalYRowSplitD18R11S11Row2,
    originalYRowSplitD18R11S11Row3,
    originalYRowSplitD18R11S11Row4,
    originalYRowSplitD18R11S11Row5,
    originalYRowSplitD18R11S11Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R11S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
