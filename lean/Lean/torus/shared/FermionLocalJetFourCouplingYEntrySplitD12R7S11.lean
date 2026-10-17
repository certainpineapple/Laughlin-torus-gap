import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R7S11Row0 :
    OAI.Laughlin.Certificate.yRow 12 7 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((4363941550291559775 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S11Row1 :
    OAI.Laughlin.Certificate.yRow 12 7 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((80593356669934603275 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S11Row2 :
    OAI.Laughlin.Certificate.yRow 12 7 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-221840553963964402603125 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S11Row3 :
    OAI.Laughlin.Certificate.yRow 12 7 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-115956887692664689572825 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S11Row4 :
    OAI.Laughlin.Certificate.yRow 12 7 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((30961229178880983299625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S11Row5 :
    OAI.Laughlin.Certificate.yRow 12 7 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((7527017748919410445275 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R7S11Row6 :
    OAI.Laughlin.Certificate.yRow 12 7 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-105449800512491178975 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R7S11 :
    OAI.Laughlin.Certificate.errorRational 12 (3 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (3 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 7 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R7S11Row0,
    originalYRowSplitD12R7S11Row1,
    originalYRowSplitD12R7S11Row2,
    originalYRowSplitD12R7S11Row3,
    originalYRowSplitD12R7S11Row4,
    originalYRowSplitD12R7S11Row5,
    originalYRowSplitD12R7S11Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R7S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
