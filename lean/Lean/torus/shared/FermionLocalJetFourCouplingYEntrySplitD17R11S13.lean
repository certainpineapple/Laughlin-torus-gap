import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R11S13Row0 :
    OAI.Laughlin.Certificate.yRow 17 11 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S13Row1 :
    OAI.Laughlin.Certificate.yRow 17 11 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-155510103227514910875 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S13Row2 :
    OAI.Laughlin.Certificate.yRow 17 11 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-301788625357444019169375 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S13Row3 :
    OAI.Laughlin.Certificate.yRow 17 11 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-69857647019781828582375 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S13Row4 :
    OAI.Laughlin.Certificate.yRow 17 11 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-103538576851145668571625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S13Row5 :
    OAI.Laughlin.Certificate.yRow 17 11 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-15940433596056855634051875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R11S13Row6 :
    OAI.Laughlin.Certificate.yRow 17 11 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((69840553159751874625125 / 256) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R11S13 :
    OAI.Laughlin.Certificate.errorRational 17 (5 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (5 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 11 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R11S13Row0,
    originalYRowSplitD17R11S13Row1,
    originalYRowSplitD17R11S13Row2,
    originalYRowSplitD17R11S13Row3,
    originalYRowSplitD17R11S13Row4,
    originalYRowSplitD17R11S13Row5,
    originalYRowSplitD17R11S13Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R11S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
