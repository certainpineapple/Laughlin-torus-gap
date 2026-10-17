import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD6R5S5Row0 :
    OAI.Laughlin.Certificate.yRow 6 5 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-12683159403402225 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R5S5Row1 :
    OAI.Laughlin.Certificate.yRow 6 5 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((3443341286073350301 / 29360128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R5S5Row2 :
    OAI.Laughlin.Certificate.yRow 6 5 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((14238813888061234251405 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R5S5Row3 :
    OAI.Laughlin.Certificate.yRow 6 5 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((3192388034526360393545 / 58720256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R5S5Row4 :
    OAI.Laughlin.Certificate.yRow 6 5 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((16165976965392307029015 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R5S5Row5 :
    OAI.Laughlin.Certificate.yRow 6 5 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-438019607995404079354925 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R5S5Row6 :
    OAI.Laughlin.Certificate.yRow 6 5 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-49530798460281753825 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD6R5S5 :
    OAI.Laughlin.Certificate.errorRational 6 (2 : Fin 3) (2 : Fin 3) =
      TorusLean.FermionM3.errorTable06 (2 : Fin 3) (2 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 6 5 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD6R5S5Row0,
    originalYRowSplitD6R5S5Row1,
    originalYRowSplitD6R5S5Row2,
    originalYRowSplitD6R5S5Row3,
    originalYRowSplitD6R5S5Row4,
    originalYRowSplitD6R5S5Row5,
    originalYRowSplitD6R5S5Row6]
  norm_num [TorusLean.FermionM3.errorTable06]

#print axioms originalYEntrySplitD6R5S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
