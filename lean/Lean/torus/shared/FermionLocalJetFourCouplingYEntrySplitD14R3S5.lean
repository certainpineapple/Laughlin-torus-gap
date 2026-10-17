import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 14 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((148821829734051953325 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 14 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-9085053434140916815275 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 14 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((8592575453485706970943425 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 14 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((4993934044857494188431375 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 14 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-20768023183225686835269825 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 14 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((31408013093586399067398975 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 14 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-122068031462339474444625 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R3S5 :
    OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (2 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (1 : Fin 7) (2 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R3S5Row0,
    originalYRowSplitD14R3S5Row1,
    originalYRowSplitD14R3S5Row2,
    originalYRowSplitD14R3S5Row3,
    originalYRowSplitD14R3S5Row4,
    originalYRowSplitD14R3S5Row5,
    originalYRowSplitD14R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
