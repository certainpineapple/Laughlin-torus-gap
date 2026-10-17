import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 16 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-18521622117786720707775 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 16 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-4455808044960136389525 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 16 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((172955937313399539273975 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 16 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((19323363941474602915780875 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 16 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-16411630310930798490722175 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 16 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2066322671542933531652925 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 16 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((745662555301753709945325 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R3S9 :
    OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (1 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R3S9Row0,
    originalYRowSplitD16R3S9Row1,
    originalYRowSplitD16R3S9Row2,
    originalYRowSplitD16R3S9Row3,
    originalYRowSplitD16R3S9Row4,
    originalYRowSplitD16R3S9Row5,
    originalYRowSplitD16R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
