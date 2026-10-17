import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 21 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 21 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 21 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 21 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 21 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((36225463071214541884134375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 21 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = (3015557626255293735000000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 21 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-8515227528466251509503125 / 2) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R9S9 :
    OAI.Laughlin.Certificate.errorRational 21 (4 : Fin 11) (4 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (4 : Fin 11) (4 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R9S9Row0,
    originalYRowSplitD21R9S9Row1,
    originalYRowSplitD21R9S9Row2,
    originalYRowSplitD21R9S9Row3,
    originalYRowSplitD21R9S9Row4,
    originalYRowSplitD21R9S9Row5,
    originalYRowSplitD21R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
