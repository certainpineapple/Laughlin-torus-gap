import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 17 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 17 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((222202641406338455625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 17 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((2471427223073434220765625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 17 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((2192428510601268047810625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 17 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-4936092211053253993168125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 17 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-128788739797835825216420625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 17 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-654777538361496774905625 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R7S7 :
    OAI.Laughlin.Certificate.errorRational 17 (3 : Fin 9) (3 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (3 : Fin 9) (3 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R7S7Row0,
    originalYRowSplitD17R7S7Row1,
    originalYRowSplitD17R7S7Row2,
    originalYRowSplitD17R7S7Row3,
    originalYRowSplitD17R7S7Row4,
    originalYRowSplitD17R7S7Row5,
    originalYRowSplitD17R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
