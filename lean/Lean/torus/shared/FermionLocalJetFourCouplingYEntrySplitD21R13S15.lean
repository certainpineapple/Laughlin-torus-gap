import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R13S15Row0 :
    OAI.Laughlin.Certificate.yRow 21 13 15
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R13S15Row1 :
    OAI.Laughlin.Certificate.yRow 21 13 15
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R13S15Row2 :
    OAI.Laughlin.Certificate.yRow 21 13 15
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R13S15Row3 :
    OAI.Laughlin.Certificate.yRow 21 13 15
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R13S15Row4 :
    OAI.Laughlin.Certificate.yRow 21 13 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((-148066258094121423931875 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R13S15Row5 :
    OAI.Laughlin.Certificate.yRow 21 13 15
      (OAI.Laughlin.Certificate.rows[5]!) = (-5187844928195237468160000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R13S15Row6 :
    OAI.Laughlin.Certificate.yRow 21 13 15
      (OAI.Laughlin.Certificate.rows[6]!) = (0 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R13S15 :
    OAI.Laughlin.Certificate.errorRational 21 (6 : Fin 11) (7 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (6 : Fin 11) (7 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 13 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R13S15Row0,
    originalYRowSplitD21R13S15Row1,
    originalYRowSplitD21R13S15Row2,
    originalYRowSplitD21R13S15Row3,
    originalYRowSplitD21R13S15Row4,
    originalYRowSplitD21R13S15Row5,
    originalYRowSplitD21R13S15Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R13S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
