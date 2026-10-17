import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 18 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 18 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 18 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 18 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((13962108964436313305625 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 18 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((6252188727210579984727771875 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 18 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-10882240354419234334849940625 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 18 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-122974860433334305618096875 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R5S5 :
    OAI.Laughlin.Certificate.errorRational 18 (2 : Fin 9) (2 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (2 : Fin 9) (2 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R5S5Row0,
    originalYRowSplitD18R5S5Row1,
    originalYRowSplitD18R5S5Row2,
    originalYRowSplitD18R5S5Row3,
    originalYRowSplitD18R5S5Row4,
    originalYRowSplitD18R5S5Row5,
    originalYRowSplitD18R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
