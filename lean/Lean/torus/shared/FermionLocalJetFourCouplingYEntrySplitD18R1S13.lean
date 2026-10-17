import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD18R1S13Row0 :
    OAI.Laughlin.Certificate.yRow 18 1 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S13Row1 :
    OAI.Laughlin.Certificate.yRow 18 1 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S13Row2 :
    OAI.Laughlin.Certificate.yRow 18 1 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S13Row3 :
    OAI.Laughlin.Certificate.yRow 18 1 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((5044540447173603128878125 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S13Row4 :
    OAI.Laughlin.Certificate.yRow 18 1 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((170553179380264596990199125 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S13Row5 :
    OAI.Laughlin.Certificate.yRow 18 1 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((75608097615724440355714125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD18R1S13Row6 :
    OAI.Laughlin.Certificate.yRow 18 1 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-29238508993507244748442125 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD18R1S13 :
    OAI.Laughlin.Certificate.errorRational 18 (0 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable18 (0 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 18 1 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD18R1S13Row0,
    originalYRowSplitD18R1S13Row1,
    originalYRowSplitD18R1S13Row2,
    originalYRowSplitD18R1S13Row3,
    originalYRowSplitD18R1S13Row4,
    originalYRowSplitD18R1S13Row5,
    originalYRowSplitD18R1S13Row6]
  norm_num [TorusLean.FermionM3.errorTable18]

#print axioms originalYEntrySplitD18R1S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
