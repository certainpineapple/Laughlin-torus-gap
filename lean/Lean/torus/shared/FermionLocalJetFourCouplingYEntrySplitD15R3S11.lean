import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R3S11Row0 :
    OAI.Laughlin.Certificate.yRow 15 3 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-4156704953386960018275 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S11Row1 :
    OAI.Laughlin.Certificate.yRow 15 3 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((703063362340463025825 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S11Row2 :
    OAI.Laughlin.Certificate.yRow 15 3 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-18063758674655319668201775 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S11Row3 :
    OAI.Laughlin.Certificate.yRow 15 3 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((4478173588693590798144825 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S11Row4 :
    OAI.Laughlin.Certificate.yRow 15 3 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((1245104237831912322472575 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S11Row5 :
    OAI.Laughlin.Certificate.yRow 15 3 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((30599282906795911765166325 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S11Row6 :
    OAI.Laughlin.Certificate.yRow 15 3 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((4291042718440813433175 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R3S11 :
    OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (1 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 3 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R3S11Row0,
    originalYRowSplitD15R3S11Row1,
    originalYRowSplitD15R3S11Row2,
    originalYRowSplitD15R3S11Row3,
    originalYRowSplitD15R3S11Row4,
    originalYRowSplitD15R3S11Row5,
    originalYRowSplitD15R3S11Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R3S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
