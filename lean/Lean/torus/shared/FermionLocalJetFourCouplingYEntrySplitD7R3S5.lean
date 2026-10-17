import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD7R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 7 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((11065428419616135 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 7 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((2141394541249492635 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 7 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-23803270741598517863565 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 7 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-14416679890174213591545 / 58720256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 7 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-54234982718013152865 / 7340032) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 7 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((310146766753353391486215 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD7R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 7 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-50552514240995949885 / 16777216) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD7R3S5 :
    OAI.Laughlin.Certificate.errorRational 7 (1 : Fin 4) (2 : Fin 4) =
      TorusLean.FermionM3.errorTable07 (1 : Fin 4) (2 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 7 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD7R3S5Row0,
    originalYRowSplitD7R3S5Row1,
    originalYRowSplitD7R3S5Row2,
    originalYRowSplitD7R3S5Row3,
    originalYRowSplitD7R3S5Row4,
    originalYRowSplitD7R3S5Row5,
    originalYRowSplitD7R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable07]

#print axioms originalYEntrySplitD7R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
