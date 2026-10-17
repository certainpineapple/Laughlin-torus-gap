import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 12 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((4481158373616246525 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 12 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-52084641431878123275 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 12 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-78728104214505115031925 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 12 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-20982331213370736440175 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 12 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((5502007805279789169675 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 12 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((158619636131986963380375 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 12 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-1509497676296617308525 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R5S7 :
    OAI.Laughlin.Certificate.errorRational 12 (2 : Fin 6) (3 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (2 : Fin 6) (3 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R5S7Row0,
    originalYRowSplitD12R5S7Row1,
    originalYRowSplitD12R5S7Row2,
    originalYRowSplitD12R5S7Row3,
    originalYRowSplitD12R5S7Row4,
    originalYRowSplitD12R5S7Row5,
    originalYRowSplitD12R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
