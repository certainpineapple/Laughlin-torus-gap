import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R5S11Row0 :
    OAI.Laughlin.Certificate.yRow 12 5 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-18039393607683519225 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S11Row1 :
    OAI.Laughlin.Certificate.yRow 12 5 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-87555873529218057975 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S11Row2 :
    OAI.Laughlin.Certificate.yRow 12 5 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((67937877376952061364875 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S11Row3 :
    OAI.Laughlin.Certificate.yRow 12 5 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((167774535768414380114925 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S11Row4 :
    OAI.Laughlin.Certificate.yRow 12 5 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-9672126508574407684125 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S11Row5 :
    OAI.Laughlin.Certificate.yRow 12 5 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-68287884586862869786275 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S11Row6 :
    OAI.Laughlin.Certificate.yRow 12 5 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((1727974014604158199725 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R5S11 :
    OAI.Laughlin.Certificate.errorRational 12 (2 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (2 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 5 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R5S11Row0,
    originalYRowSplitD12R5S11Row1,
    originalYRowSplitD12R5S11Row2,
    originalYRowSplitD12R5S11Row3,
    originalYRowSplitD12R5S11Row4,
    originalYRowSplitD12R5S11Row5,
    originalYRowSplitD12R5S11Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R5S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
