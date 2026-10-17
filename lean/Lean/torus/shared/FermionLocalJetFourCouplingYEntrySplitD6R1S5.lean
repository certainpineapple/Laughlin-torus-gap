import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD6R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 6 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-25337544191982945 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 6 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-64850294213833938891 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 6 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((74183602070419332929805 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 6 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-50030547718509845161435 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 6 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((12494804873696306595795 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 6 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-35057003947383105480505 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 6 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-83005876560364727985 / 33554432) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD6R1S5 :
    OAI.Laughlin.Certificate.errorRational 6 (0 : Fin 3) (2 : Fin 3) =
      TorusLean.FermionM3.errorTable06 (0 : Fin 3) (2 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 6 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD6R1S5Row0,
    originalYRowSplitD6R1S5Row1,
    originalYRowSplitD6R1S5Row2,
    originalYRowSplitD6R1S5Row3,
    originalYRowSplitD6R1S5Row4,
    originalYRowSplitD6R1S5Row5,
    originalYRowSplitD6R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable06]

#print axioms originalYEntrySplitD6R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
