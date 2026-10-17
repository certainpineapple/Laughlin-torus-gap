import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 14 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-82694640373005622136175 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 14 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-7261678679023403209575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 14 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((201851915545540313479451025 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 14 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-23481631669977288614567475 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 14 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((69528728904258929306054625 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 14 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-438198606874590097895233875 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 14 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((191226893679674481754125 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R1S5 :
    OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (2 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (0 : Fin 7) (2 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R1S5Row0,
    originalYRowSplitD14R1S5Row1,
    originalYRowSplitD14R1S5Row2,
    originalYRowSplitD14R1S5Row3,
    originalYRowSplitD14R1S5Row4,
    originalYRowSplitD14R1S5Row5,
    originalYRowSplitD14R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
