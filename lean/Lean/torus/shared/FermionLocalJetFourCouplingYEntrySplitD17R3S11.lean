import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R3S11Row0 :
    OAI.Laughlin.Certificate.yRow 17 3 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S11Row1 :
    OAI.Laughlin.Certificate.yRow 17 3 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((24666804116203983859125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S11Row2 :
    OAI.Laughlin.Certificate.yRow 17 3 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-5628925813531967958886875 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S11Row3 :
    OAI.Laughlin.Certificate.yRow 17 3 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-847332154110689532660375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S11Row4 :
    OAI.Laughlin.Certificate.yRow 17 3 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3162776471797122041486625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S11Row5 :
    OAI.Laughlin.Certificate.yRow 17 3 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((263751351805535483034770625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S11Row6 :
    OAI.Laughlin.Certificate.yRow 17 3 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2021290304224707398507625 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R3S11 :
    OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (1 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 3 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R3S11Row0,
    originalYRowSplitD17R3S11Row1,
    originalYRowSplitD17R3S11Row2,
    originalYRowSplitD17R3S11Row3,
    originalYRowSplitD17R3S11Row4,
    originalYRowSplitD17R3S11Row5,
    originalYRowSplitD17R3S11Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R3S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
