import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 21 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 21 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 21 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 21 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 21 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((2832895476763155062268384375 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 21 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = (12049917888002435040600000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 21 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-444158472935431020094453125 / 8) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R5S5 :
    OAI.Laughlin.Certificate.errorRational 21 (2 : Fin 11) (2 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (2 : Fin 11) (2 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R5S5Row0,
    originalYRowSplitD21R5S5Row1,
    originalYRowSplitD21R5S5Row2,
    originalYRowSplitD21R5S5Row3,
    originalYRowSplitD21R5S5Row4,
    originalYRowSplitD21R5S5Row5,
    originalYRowSplitD21R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
