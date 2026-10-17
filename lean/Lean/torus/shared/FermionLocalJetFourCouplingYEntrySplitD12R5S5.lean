import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 12 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-75872487415218761925 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 12 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((190996308199194292575 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 12 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((83645738170003355701275 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 12 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-134274324205288891295325 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 12 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((127453023208049701662225 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 12 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-419019957221155972103475 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 12 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-10705530294802827217125 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R5S5 :
    OAI.Laughlin.Certificate.errorRational 12 (2 : Fin 6) (2 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (2 : Fin 6) (2 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R5S5Row0,
    originalYRowSplitD12R5S5Row1,
    originalYRowSplitD12R5S5Row2,
    originalYRowSplitD12R5S5Row3,
    originalYRowSplitD12R5S5Row4,
    originalYRowSplitD12R5S5Row5,
    originalYRowSplitD12R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
