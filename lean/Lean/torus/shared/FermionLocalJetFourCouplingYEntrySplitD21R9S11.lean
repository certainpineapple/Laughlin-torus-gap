import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R9S11Row0 :
    OAI.Laughlin.Certificate.yRow 21 9 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S11Row1 :
    OAI.Laughlin.Certificate.yRow 21 9 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S11Row2 :
    OAI.Laughlin.Certificate.yRow 21 9 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S11Row3 :
    OAI.Laughlin.Certificate.yRow 21 9 11
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S11Row4 :
    OAI.Laughlin.Certificate.yRow 21 9 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-17374944140130077222596875 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S11Row5 :
    OAI.Laughlin.Certificate.yRow 21 9 11
      (OAI.Laughlin.Certificate.rows[5]!) = (-3132251136534746803500000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S11Row6 :
    OAI.Laughlin.Certificate.yRow 21 9 11
      (OAI.Laughlin.Certificate.rows[6]!) = (2838409176155417169834375 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R9S11 :
    OAI.Laughlin.Certificate.errorRational 21 (4 : Fin 11) (5 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (4 : Fin 11) (5 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 9 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R9S11Row0,
    originalYRowSplitD21R9S11Row1,
    originalYRowSplitD21R9S11Row2,
    originalYRowSplitD21R9S11Row3,
    originalYRowSplitD21R9S11Row4,
    originalYRowSplitD21R9S11Row5,
    originalYRowSplitD21R9S11Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R9S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
