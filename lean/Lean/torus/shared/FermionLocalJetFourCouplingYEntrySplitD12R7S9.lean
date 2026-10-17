import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R7S9Row0 :
    OAI.Laughlin.Certificate.yRow 12 7 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((19922185633547009925 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S9Row1 :
    OAI.Laughlin.Certificate.yRow 12 7 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-52927764881751856575 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S9Row2 :
    OAI.Laughlin.Certificate.yRow 12 7 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((51727873644997577700075 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S9Row3 :
    OAI.Laughlin.Certificate.yRow 12 7 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((5886080899351474025925 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S9Row4 :
    OAI.Laughlin.Certificate.yRow 12 7 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-408835020360997373625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S9Row5 :
    OAI.Laughlin.Certificate.yRow 12 7 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-65771734461391793070225 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S9Row6 :
    OAI.Laughlin.Certificate.yRow 12 7 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((212265127672800077925 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R7S9 :
    OAI.Laughlin.Certificate.errorRational 12 (3 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (3 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 7 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R7S9Row0,
    originalYRowSplitD12R7S9Row1,
    originalYRowSplitD12R7S9Row2,
    originalYRowSplitD12R7S9Row3,
    originalYRowSplitD12R7S9Row4,
    originalYRowSplitD12R7S9Row5,
    originalYRowSplitD12R7S9Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R7S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
