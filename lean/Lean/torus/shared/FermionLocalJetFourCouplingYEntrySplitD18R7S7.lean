import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R7S7Row0 :
    OAI.Laughlin.Certificate.yRow 18 7 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S7Row1 :
    OAI.Laughlin.Certificate.yRow 18 7 7
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S7Row2 :
    OAI.Laughlin.Certificate.yRow 18 7 7
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S7Row3 :
    OAI.Laughlin.Certificate.yRow 18 7 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((538754998787765158100625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S7Row4 :
    OAI.Laughlin.Certificate.yRow 18 7 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((504131184225476248559146875 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S7Row5 :
    OAI.Laughlin.Certificate.yRow 18 7 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1027526096433006892279490625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R7S7Row6 :
    OAI.Laughlin.Certificate.yRow 18 7 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-18127619867659536967280625 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R7S7 :
    OAI.Laughlin.Certificate.errorRational 18 (3 : Fin 9) (3 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (3 : Fin 9) (3 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 7 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R7S7Row0,
    originalYRowSplitD18R7S7Row1,
    originalYRowSplitD18R7S7Row2,
    originalYRowSplitD18R7S7Row3,
    originalYRowSplitD18R7S7Row4,
    originalYRowSplitD18R7S7Row5,
    originalYRowSplitD18R7S7Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R7S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
