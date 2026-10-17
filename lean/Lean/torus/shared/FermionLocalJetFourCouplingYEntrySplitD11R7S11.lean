import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R7S11Row0 :
    OAI.Laughlin.Certificate.yRow 11 7 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-12133336653147627225 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S11Row1 :
    OAI.Laughlin.Certificate.yRow 11 7 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((326182545168457319595 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S11Row2 :
    OAI.Laughlin.Certificate.yRow 11 7 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((185847570659267212333275 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S11Row3 :
    OAI.Laughlin.Certificate.yRow 11 7 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-24282534750125311338525 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S11Row4 :
    OAI.Laughlin.Certificate.yRow 11 7 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-337731090954997234275 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S11Row5 :
    OAI.Laughlin.Certificate.yRow 11 7 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-69013081999713687692175 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R7S11Row6 :
    OAI.Laughlin.Certificate.yRow 11 7 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-320277735293634397125 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R7S11 :
    OAI.Laughlin.Certificate.errorRational 11 (3 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (3 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 7 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R7S11Row0,
    originalYRowSplitD11R7S11Row1,
    originalYRowSplitD11R7S11Row2,
    originalYRowSplitD11R7S11Row3,
    originalYRowSplitD11R7S11Row4,
    originalYRowSplitD11R7S11Row5,
    originalYRowSplitD11R7S11Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R7S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
