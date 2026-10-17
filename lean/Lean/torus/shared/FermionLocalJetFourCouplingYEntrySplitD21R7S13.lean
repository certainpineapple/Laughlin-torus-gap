import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD21R7S13Row0 :
    OAI.Laughlin.Certificate.yRow 21 7 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S13Row1 :
    OAI.Laughlin.Certificate.yRow 21 7 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S13Row2 :
    OAI.Laughlin.Certificate.yRow 21 7 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S13Row3 :
    OAI.Laughlin.Certificate.yRow 21 7 13
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S13Row4 :
    OAI.Laughlin.Certificate.yRow 21 7 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((6552986179496933811009375 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S13Row5 :
    OAI.Laughlin.Certificate.yRow 21 7 13
      (OAI.Laughlin.Certificate.rows[5]!) = (-4561443124989035725440000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD21R7S13Row6 :
    OAI.Laughlin.Certificate.yRow 21 7 13
      (OAI.Laughlin.Certificate.rows[6]!) = (2763652720487126347254375 : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD21R7S13 :
    OAI.Laughlin.Certificate.errorRational 21 (3 : Fin 11) (6 : Fin 11) =
      TorusLean.FermionM3.errorTable21 (3 : Fin 11) (6 : Fin 11) := by
  change OAI.Laughlin.Certificate.Y 21 7 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD21R7S13Row0,
    originalYRowSplitD21R7S13Row1,
    originalYRowSplitD21R7S13Row2,
    originalYRowSplitD21R7S13Row3,
    originalYRowSplitD21R7S13Row4,
    originalYRowSplitD21R7S13Row5,
    originalYRowSplitD21R7S13Row6]
  norm_num [TorusLean.FermionM3.errorTable21]

#print axioms originalYEntrySplitD21R7S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
