import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 19 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 19 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 19 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 19 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 19 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-10816898040513256732754088375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 19 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((48026883033850245239555465625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 19 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-359803139160604094366536125 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R1S11 :
    OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (5 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (0 : Fin 10) (5 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R1S11Row0,
    originalYRowSplitD19R1S11Row1,
    originalYRowSplitD19R1S11Row2,
    originalYRowSplitD19R1S11Row3,
    originalYRowSplitD19R1S11Row4,
    originalYRowSplitD19R1S11Row5,
    originalYRowSplitD19R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
