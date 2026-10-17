import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 13 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-124944414023732384025 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 13 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-363008795360883332175 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 13 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-394070110555723389014175 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 13 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((43180767981560231849925 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 13 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-476212772011258196458425 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 13 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((3906958751391612546003825 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 13 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((6091088420891523503475 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R5S7 :
    OAI.Laughlin.Certificate.errorRational 13 (2 : Fin 7) (3 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (2 : Fin 7) (3 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R5S7Row0,
    originalYRowSplitD13R5S7Row1,
    originalYRowSplitD13R5S7Row2,
    originalYRowSplitD13R5S7Row3,
    originalYRowSplitD13R5S7Row4,
    originalYRowSplitD13R5S7Row5,
    originalYRowSplitD13R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
