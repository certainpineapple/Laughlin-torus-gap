import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 21 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 21 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 21 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 21 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 21 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-4924582697042063247426609375 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 21 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = (-7323943442494722405862500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 21 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((207273954036534476044078125 / 8) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R5S7 :
    OAI.Laughlin.Certificate.errorRational 21 (2 : Fin 11) (3 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (2 : Fin 11) (3 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R5S7Row0,
    originalYRowSplitD21R5S7Row1,
    originalYRowSplitD21R5S7Row2,
    originalYRowSplitD21R5S7Row3,
    originalYRowSplitD21R5S7Row4,
    originalYRowSplitD21R5S7Row5,
    originalYRowSplitD21R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
