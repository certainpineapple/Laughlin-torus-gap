import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 21 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 21 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 21 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 21 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 21 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((8560681090753012512150234375 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 21 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((17805979442322522034959375 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 21 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-96727845217049422153903125 / 8) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R7S7 :
    OAI.Laughlin.Certificate.errorRational 21 (3 : Fin 11) (3 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (3 : Fin 11) (3 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R7S7Row0,
    originalYRowSplitD21R7S7Row1,
    originalYRowSplitD21R7S7Row2,
    originalYRowSplitD21R7S7Row3,
    originalYRowSplitD21R7S7Row4,
    originalYRowSplitD21R7S7Row5,
    originalYRowSplitD21R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
