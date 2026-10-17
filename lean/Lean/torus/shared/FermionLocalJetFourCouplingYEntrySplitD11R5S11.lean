import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R5S11Row0 :
    OAI.Laughlin.Certificate.yRow 11 5 11
      (OAI.Laughlin.Certificate.rows[0]!) = (-581996346039246600 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S11Row1 :
    OAI.Laughlin.Certificate.yRow 11 5 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-210743796284128500525 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S11Row2 :
    OAI.Laughlin.Certificate.yRow 11 5 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((638706384284993972008875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S11Row3 :
    OAI.Laughlin.Certificate.yRow 11 5 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((80119963139402783953125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S11Row4 :
    OAI.Laughlin.Certificate.yRow 11 5 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-94443531638846515366725 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S11Row5 :
    OAI.Laughlin.Certificate.yRow 11 5 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-207452729266581268431225 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R5S11Row6 :
    OAI.Laughlin.Certificate.yRow 11 5 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-6990175315174318811775 / 131072) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R5S11 :
    OAI.Laughlin.Certificate.errorRational 11 (2 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (2 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 5 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R5S11Row0,
    originalYRowSplitD11R5S11Row1,
    originalYRowSplitD11R5S11Row2,
    originalYRowSplitD11R5S11Row3,
    originalYRowSplitD11R5S11Row4,
    originalYRowSplitD11R5S11Row5,
    originalYRowSplitD11R5S11Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R5S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
