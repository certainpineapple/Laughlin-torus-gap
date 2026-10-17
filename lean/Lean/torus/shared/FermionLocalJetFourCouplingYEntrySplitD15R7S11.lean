import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R7S11Row0 :
    OAI.Laughlin.Certificate.yRow 15 7 11
      (OAI.Laughlin.Certificate.rows[0]!) = (379792799447683596975 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S11Row1 :
    OAI.Laughlin.Certificate.yRow 15 7 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-858249767247053972175 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S11Row2 :
    OAI.Laughlin.Certificate.yRow 15 7 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((3696517256905260480179025 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S11Row3 :
    OAI.Laughlin.Certificate.yRow 15 7 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-20201116508738669178675 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S11Row4 :
    OAI.Laughlin.Certificate.yRow 15 7 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((81277831894241479248675 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S11Row5 :
    OAI.Laughlin.Certificate.yRow 15 7 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((1981741979295884595237525 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R7S11Row6 :
    OAI.Laughlin.Certificate.yRow 15 7 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-18524443122401637180375 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R7S11 :
    OAI.Laughlin.Certificate.errorRational 15 (3 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (3 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 7 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R7S11Row0,
    originalYRowSplitD15R7S11Row1,
    originalYRowSplitD15R7S11Row2,
    originalYRowSplitD15R7S11Row3,
    originalYRowSplitD15R7S11Row4,
    originalYRowSplitD15R7S11Row5,
    originalYRowSplitD15R7S11Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R7S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
