import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 15 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((-113902428507078585649275 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 15 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((86862046660672041383625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 15 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-119913549723119526570971775 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 15 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-23366685339283842601370325 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 15 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-264365526308521574226264975 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 15 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((491572116009500097695698575 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 15 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((1021685520386605155906825 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R1S7 :
    OAI.Laughlin.Certificate.errorRational 15 (0 : Fin 8) (3 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (0 : Fin 8) (3 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R1S7Row0,
    originalYRowSplitD15R1S7Row1,
    originalYRowSplitD15R1S7Row2,
    originalYRowSplitD15R1S7Row3,
    originalYRowSplitD15R1S7Row4,
    originalYRowSplitD15R1S7Row5,
    originalYRowSplitD15R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
