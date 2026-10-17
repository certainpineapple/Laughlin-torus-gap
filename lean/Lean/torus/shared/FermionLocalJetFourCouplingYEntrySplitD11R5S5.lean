import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 11 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((24524819424177951375 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 11 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-31289951408950853325 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 11 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-476333627620615001972325 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 11 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-15273420151414549799025 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 11 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((30619824690598215841125 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 11 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-486051585153873869182275 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 11 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((5393164149393265242225 / 4194304) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R5S5 :
    OAI.Laughlin.Certificate.errorRational 11 (2 : Fin 6) (2 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (2 : Fin 6) (2 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R5S5Row0,
    originalYRowSplitD11R5S5Row1,
    originalYRowSplitD11R5S5Row2,
    originalYRowSplitD11R5S5Row3,
    originalYRowSplitD11R5S5Row4,
    originalYRowSplitD11R5S5Row5,
    originalYRowSplitD11R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
