import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R9S9Row0 :
    OAI.Laughlin.Certificate.yRow 15 9 9
      (OAI.Laughlin.Certificate.rows[0]!) = (229979119566620799900 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S9Row1 :
    OAI.Laughlin.Certificate.yRow 15 9 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((1164449225197704044025 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S9Row2 :
    OAI.Laughlin.Certificate.yRow 15 9 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-274299503224939829369775 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S9Row3 :
    OAI.Laughlin.Certificate.yRow 15 9 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((523986036715214833383225 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S9Row4 :
    OAI.Laughlin.Certificate.yRow 15 9 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((318829738780461663830025 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S9Row5 :
    OAI.Laughlin.Certificate.yRow 15 9 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((2166775154156431474152525 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R9S9Row6 :
    OAI.Laughlin.Certificate.yRow 15 9 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((8115136872615819369225 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R9S9 :
    OAI.Laughlin.Certificate.errorRational 15 (4 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (4 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 9 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R9S9Row0,
    originalYRowSplitD15R9S9Row1,
    originalYRowSplitD15R9S9Row2,
    originalYRowSplitD15R9S9Row3,
    originalYRowSplitD15R9S9Row4,
    originalYRowSplitD15R9S9Row5,
    originalYRowSplitD15R9S9Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R9S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
