import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD10R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 10 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-49404171403690249545 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 10 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-15641499159082742265 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 10 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-65583088234805315943585 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 10 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-24678759801670003124865 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 10 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-80818062389353598081085 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 10 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-250320018020499737545905 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD10R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 10 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-5056883592990284495475 / 2097152) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD10R3S7 :
    OAI.Laughlin.Certificate.errorRational 10 (1 : Fin 5) (3 : Fin 5) =
      TorusLean.FermionM3.errorTable10 (1 : Fin 5) (3 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 10 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD10R3S7Row0,
    originalYRowSplitD10R3S7Row1,
    originalYRowSplitD10R3S7Row2,
    originalYRowSplitD10R3S7Row3,
    originalYRowSplitD10R3S7Row4,
    originalYRowSplitD10R3S7Row5,
    originalYRowSplitD10R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable10]

#print axioms originalYEntrySplitD10R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
