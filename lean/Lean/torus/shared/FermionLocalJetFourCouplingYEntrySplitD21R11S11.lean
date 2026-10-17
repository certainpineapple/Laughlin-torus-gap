import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R11S11Row0 :
    OAI.Laughlin.Certificate.yRow 21 11 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S11Row1 :
    OAI.Laughlin.Certificate.yRow 21 11 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S11Row2 :
    OAI.Laughlin.Certificate.yRow 21 11 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S11Row3 :
    OAI.Laughlin.Certificate.yRow 21 11 11
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S11Row4 :
    OAI.Laughlin.Certificate.yRow 21 11 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((8333604549903659707209375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S11Row5 :
    OAI.Laughlin.Certificate.yRow 21 11 11
      (OAI.Laughlin.Certificate.rows[5]!) = (3253460354032917763350000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R11S11Row6 :
    OAI.Laughlin.Certificate.yRow 21 11 11
      (OAI.Laughlin.Certificate.rows[6]!) = (-1892272784103611446556250 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R11S11 :
    OAI.Laughlin.Certificate.errorRational 21 (5 : Fin 11) (5 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (5 : Fin 11) (5 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 11 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R11S11Row0,
    originalYRowSplitD21R11S11Row1,
    originalYRowSplitD21R11S11Row2,
    originalYRowSplitD21R11S11Row3,
    originalYRowSplitD21R11S11Row4,
    originalYRowSplitD21R11S11Row5,
    originalYRowSplitD21R11S11Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R11S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
