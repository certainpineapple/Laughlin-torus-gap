import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD8R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 8 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-2191463802492555735 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 8 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((2321948566914231201 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 8 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((106818877845876879555 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 8 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((2894465599178455021275 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 8 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((17756957755544037975 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 8 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((607875903328624705389525 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD8R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 8 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((14119266506282124255 / 2097152) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD8R5S5 :
    OAI.Laughlin.Certificate.errorRational 8 (2 : Fin 4) (2 : Fin 4) =
      TorusLean.FermionM3.errorTable08 (2 : Fin 4) (2 : Fin 4) := by
  change OAI.Laughlin.Certificate.Y 8 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD8R5S5Row0,
    originalYRowSplitD8R5S5Row1,
    originalYRowSplitD8R5S5Row2,
    originalYRowSplitD8R5S5Row3,
    originalYRowSplitD8R5S5Row4,
    originalYRowSplitD8R5S5Row5,
    originalYRowSplitD8R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable08]

#print axioms originalYEntrySplitD8R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
