import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 16 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((112071605702450625 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 16 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((828412131836430532125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 16 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((808842254299870871907225 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 16 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((3141046164264001294692825 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 16 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((10650752475568004082822525 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 16 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2178566590592142537061275 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 16 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-378361553672598899843475 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R7S7 :
    OAI.Laughlin.Certificate.errorRational 16 (3 : Fin 8) (3 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (3 : Fin 8) (3 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R7S7Row0,
    originalYRowSplitD16R7S7Row1,
    originalYRowSplitD16R7S7Row2,
    originalYRowSplitD16R7S7Row3,
    originalYRowSplitD16R7S7Row4,
    originalYRowSplitD16R7S7Row5,
    originalYRowSplitD16R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
