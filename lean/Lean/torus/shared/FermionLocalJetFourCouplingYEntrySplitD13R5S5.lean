import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 13 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((114330143706106823775 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 13 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((936235603993925219625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 13 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((643923128460363065060625 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 13 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((55787384995979625889875 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 13 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-339750254582968729465125 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 13 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-6702422820092401487530725 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 13 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-168453910544722999029225 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R5S5 :
    OAI.Laughlin.Certificate.errorRational 13 (2 : Fin 7) (2 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (2 : Fin 7) (2 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R5S5Row0,
    originalYRowSplitD13R5S5Row1,
    originalYRowSplitD13R5S5Row2,
    originalYRowSplitD13R5S5Row3,
    originalYRowSplitD13R5S5Row4,
    originalYRowSplitD13R5S5Row5,
    originalYRowSplitD13R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
