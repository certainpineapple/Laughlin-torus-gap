import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 9 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((101561083815787002225 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 9 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((1179997330982166194301 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 9 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((121215547319209813119285 / 33554432) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 9 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((-130879700072685286403565 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 9 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((-55049070779469695669205 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 9 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((447006909545182523501805 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 9 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-34693449211761003462645 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R1S1 :
    OAI.Laughlin.Certificate.errorRational 9 (0 : Fin 5) (0 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (0 : Fin 5) (0 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R1S1Row0,
    originalYRowSplitD9R1S1Row1,
    originalYRowSplitD9R1S1Row2,
    originalYRowSplitD9R1S1Row3,
    originalYRowSplitD9R1S1Row4,
    originalYRowSplitD9R1S1Row5,
    originalYRowSplitD9R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
