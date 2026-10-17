import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R5S9Row0 :
    OAI.Laughlin.Certificate.yRow 12 5 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((44790671475382056525 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S9Row1 :
    OAI.Laughlin.Certificate.yRow 12 5 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((55645337159398426275 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S9Row2 :
    OAI.Laughlin.Certificate.yRow 12 5 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((-96938771212376419724325 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S9Row3 :
    OAI.Laughlin.Certificate.yRow 12 5 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((31433421896311748910975 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S9Row4 :
    OAI.Laughlin.Certificate.yRow 12 5 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((-16600290838703933402025 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S9Row5 :
    OAI.Laughlin.Certificate.yRow 12 5 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((383641746677681091862725 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S9Row6 :
    OAI.Laughlin.Certificate.yRow 12 5 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((1083504957909314769675 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R5S9 :
    OAI.Laughlin.Certificate.errorRational 12 (2 : Fin 6) (4 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (2 : Fin 6) (4 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 5 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R5S9Row0,
    originalYRowSplitD12R5S9Row1,
    originalYRowSplitD12R5S9Row2,
    originalYRowSplitD12R5S9Row3,
    originalYRowSplitD12R5S9Row4,
    originalYRowSplitD12R5S9Row5,
    originalYRowSplitD12R5S9Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R5S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
