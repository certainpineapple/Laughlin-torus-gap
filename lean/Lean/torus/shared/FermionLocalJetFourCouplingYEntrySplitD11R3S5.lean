import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 11 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-422454170492661825 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 11 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((99753573560099022675 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 11 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((1319605187195201661736875 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 11 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((124841851987839113015325 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 11 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((67481304536970339395625 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 11 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((789597547898464348541775 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 11 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((205654659644207990475 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R3S5 :
    OAI.Laughlin.Certificate.errorRational 11 (1 : Fin 6) (2 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (1 : Fin 6) (2 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R3S5Row0,
    originalYRowSplitD11R3S5Row1,
    originalYRowSplitD11R3S5Row2,
    originalYRowSplitD11R3S5Row3,
    originalYRowSplitD11R3S5Row4,
    originalYRowSplitD11R3S5Row5,
    originalYRowSplitD11R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
