import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R7S11Row0 :
    OAI.Laughlin.Certificate.yRow 13 7 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-98448079225704186825 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S11Row1 :
    OAI.Laughlin.Certificate.yRow 13 7 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-227971666542707943075 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S11Row2 :
    OAI.Laughlin.Certificate.yRow 13 7 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-333938993713145752686975 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S11Row3 :
    OAI.Laughlin.Certificate.yRow 13 7 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-38454002066233509819525 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S11Row4 :
    OAI.Laughlin.Certificate.yRow 13 7 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((5058113966660812308075 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S11Row5 :
    OAI.Laughlin.Certificate.yRow 13 7 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-318741912859543824679875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S11Row6 :
    OAI.Laughlin.Certificate.yRow 13 7 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((1265105446127009816175 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R7S11 :
    OAI.Laughlin.Certificate.errorRational 13 (3 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (3 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 7 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R7S11Row0,
    originalYRowSplitD13R7S11Row1,
    originalYRowSplitD13R7S11Row2,
    originalYRowSplitD13R7S11Row3,
    originalYRowSplitD13R7S11Row4,
    originalYRowSplitD13R7S11Row5,
    originalYRowSplitD13R7S11Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R7S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
