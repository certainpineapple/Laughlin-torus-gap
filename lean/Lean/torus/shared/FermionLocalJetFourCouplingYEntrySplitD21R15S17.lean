import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R15S17Row0 :
    OAI.Laughlin.Certificate.yRow 21 15 17
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R15S17Row1 :
    OAI.Laughlin.Certificate.yRow 21 15 17
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R15S17Row2 :
    OAI.Laughlin.Certificate.yRow 21 15 17
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R15S17Row3 :
    OAI.Laughlin.Certificate.yRow 21 15 17
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R15S17Row4 :
    OAI.Laughlin.Certificate.yRow 21 15 17
      (OAI.Laughlin.Certificate.rows[4]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R15S17Row5 :
    OAI.Laughlin.Certificate.yRow 21 15 17
      (OAI.Laughlin.Certificate.rows[5]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R15S17Row6 :
    OAI.Laughlin.Certificate.yRow 21 15 17
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R15S17 :
    OAI.Laughlin.Certificate.errorRational 21 (7 : Fin 11) (8 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (7 : Fin 11) (8 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 15 17 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R15S17Row0,
    originalYRowSplitD21R15S17Row1,
    originalYRowSplitD21R15S17Row2,
    originalYRowSplitD21R15S17Row3,
    originalYRowSplitD21R15S17Row4,
    originalYRowSplitD21R15S17Row5,
    originalYRowSplitD21R15S17Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R15S17
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
