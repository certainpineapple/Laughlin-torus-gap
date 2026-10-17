import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R3S17Row0 :
    OAI.Laughlin.Certificate.yRow 17 3 17
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S17Row1 :
    OAI.Laughlin.Certificate.yRow 17 3 17
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S17Row2 :
    OAI.Laughlin.Certificate.yRow 17 3 17
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S17Row3 :
    OAI.Laughlin.Certificate.yRow 17 3 17
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S17Row4 :
    OAI.Laughlin.Certificate.yRow 17 3 17
      (OAI.Laughlin.Certificate.rows[4]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S17Row5 :
    OAI.Laughlin.Certificate.yRow 17 3 17
      (OAI.Laughlin.Certificate.rows[5]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S17Row6 :
    OAI.Laughlin.Certificate.yRow 17 3 17
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R3S17 :
    OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (8 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (1 : Fin 9) (8 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 3 17 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R3S17Row0,
    originalYRowSplitD17R3S17Row1,
    originalYRowSplitD17R3S17Row2,
    originalYRowSplitD17R3S17Row3,
    originalYRowSplitD17R3S17Row4,
    originalYRowSplitD17R3S17Row5,
    originalYRowSplitD17R3S17Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R3S17
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
