import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 17 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 17 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-1228633992219992573840625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 17 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-141120209597015124441590625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 17 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((15354325598721124640625 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 17 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((7473588658035046730189881875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 17 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-43184987524308883587282073125 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 17 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-628509757635439781420694375 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R1S5 :
    OAI.Laughlin.Certificate.errorRational 17 (0 : Fin 9) (2 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (0 : Fin 9) (2 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R1S5Row0,
    originalYRowSplitD17R1S5Row1,
    originalYRowSplitD17R1S5Row2,
    originalYRowSplitD17R1S5Row3,
    originalYRowSplitD17R1S5Row4,
    originalYRowSplitD17R1S5Row5,
    originalYRowSplitD17R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
