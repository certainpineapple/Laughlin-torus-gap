import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 14 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((4725166261180666610925 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 14 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-3791281273720050223575 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 14 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-4670473288401679668022575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 14 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((1140422085389061089116425 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 14 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((2345453806474425791927475 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 14 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((4369683854964008476197225 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 14 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1255114523153106066198825 / 131072) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R3S7 :
    OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (3 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (1 : Fin 7) (3 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R3S7Row0,
    originalYRowSplitD14R3S7Row1,
    originalYRowSplitD14R3S7Row2,
    originalYRowSplitD14R3S7Row3,
    originalYRowSplitD14R3S7Row4,
    originalYRowSplitD14R3S7Row5,
    originalYRowSplitD14R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
