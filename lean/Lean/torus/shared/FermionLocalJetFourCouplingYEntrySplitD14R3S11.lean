import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R3S11Row0 :
    OAI.Laughlin.Certificate.yRow 14 3 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((5903205814159621038225 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S11Row1 :
    OAI.Laughlin.Certificate.yRow 14 3 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-2559428325211642228575 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S11Row2 :
    OAI.Laughlin.Certificate.yRow 14 3 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-5116599424473714078137775 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S11Row3 :
    OAI.Laughlin.Certificate.yRow 14 3 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((64675795338603213967125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S11Row4 :
    OAI.Laughlin.Certificate.yRow 14 3 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2261737185950276947318725 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S11Row5 :
    OAI.Laughlin.Certificate.yRow 14 3 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-4888807299323193148276275 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S11Row6 :
    OAI.Laughlin.Certificate.yRow 14 3 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-606834292636122347637225 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R3S11 :
    OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (1 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 3 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R3S11Row0,
    originalYRowSplitD14R3S11Row1,
    originalYRowSplitD14R3S11Row2,
    originalYRowSplitD14R3S11Row3,
    originalYRowSplitD14R3S11Row4,
    originalYRowSplitD14R3S11Row5,
    originalYRowSplitD14R3S11Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R3S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
