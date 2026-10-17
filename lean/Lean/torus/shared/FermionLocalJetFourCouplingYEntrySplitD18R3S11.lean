import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R3S11Row0 :
    OAI.Laughlin.Certificate.yRow 18 3 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S11Row1 :
    OAI.Laughlin.Certificate.yRow 18 3 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S11Row2 :
    OAI.Laughlin.Certificate.yRow 18 3 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S11Row3 :
    OAI.Laughlin.Certificate.yRow 18 3 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((39802672007604404058785625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S11Row4 :
    OAI.Laughlin.Certificate.yRow 18 3 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((77001130459612792757449125 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S11Row5 :
    OAI.Laughlin.Certificate.yRow 18 3 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-658656682282986265020767625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R3S11Row6 :
    OAI.Laughlin.Certificate.yRow 18 3 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-25196584989495110762946375 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R3S11 :
    OAI.Laughlin.Certificate.errorRational 18 (1 : Fin 9) (5 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (1 : Fin 9) (5 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 3 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R3S11Row0,
    originalYRowSplitD18R3S11Row1,
    originalYRowSplitD18R3S11Row2,
    originalYRowSplitD18R3S11Row3,
    originalYRowSplitD18R3S11Row4,
    originalYRowSplitD18R3S11Row5,
    originalYRowSplitD18R3S11Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R3S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
