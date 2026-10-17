import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R5S15Row0 :
    OAI.Laughlin.Certificate.yRow 16 5 15
      (OAI.Laughlin.Certificate.rows[0]!) = (16573843549740281805000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S15Row1 :
    OAI.Laughlin.Certificate.yRow 16 5 15
      (OAI.Laughlin.Certificate.rows[1]!) = ((-9509800925058332023125 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S15Row2 :
    OAI.Laughlin.Certificate.yRow 16 5 15
      (OAI.Laughlin.Certificate.rows[2]!) = ((-1187063750415244935358125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S15Row3 :
    OAI.Laughlin.Certificate.yRow 16 5 15
      (OAI.Laughlin.Certificate.rows[3]!) = ((13265836797844081322746875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S15Row4 :
    OAI.Laughlin.Certificate.yRow 16 5 15
      (OAI.Laughlin.Certificate.rows[4]!) = ((11567309251730228972600625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S15Row5 :
    OAI.Laughlin.Certificate.yRow 16 5 15
      (OAI.Laughlin.Certificate.rows[5]!) = ((330730937294134332351020625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S15Row6 :
    OAI.Laughlin.Certificate.yRow 16 5 15
      (OAI.Laughlin.Certificate.rows[6]!) = ((88336657631745061914375 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R5S15 :
    OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (7 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (2 : Fin 8) (7 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 5 15 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R5S15Row0,
    originalYRowSplitD16R5S15Row1,
    originalYRowSplitD16R5S15Row2,
    originalYRowSplitD16R5S15Row3,
    originalYRowSplitD16R5S15Row4,
    originalYRowSplitD16R5S15Row5,
    originalYRowSplitD16R5S15Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R5S15
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
