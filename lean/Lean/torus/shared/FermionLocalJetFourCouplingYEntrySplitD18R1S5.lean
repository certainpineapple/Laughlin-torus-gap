import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 18 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 18 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 18 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 18 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-8733891600198724262428125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 18 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((38270165195540567144767786875 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 18 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-154041010028665154604677593125 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 18 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((1333551315541152681350251875 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R1S5 :
    OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (2 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (0 : Fin 9) (2 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R1S5Row0,
    originalYRowSplitD18R1S5Row1,
    originalYRowSplitD18R1S5Row2,
    originalYRowSplitD18R1S5Row3,
    originalYRowSplitD18R1S5Row4,
    originalYRowSplitD18R1S5Row5,
    originalYRowSplitD18R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
