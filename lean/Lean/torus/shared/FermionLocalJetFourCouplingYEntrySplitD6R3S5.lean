import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD6R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 6 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((1022665626893128275 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 6 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-12392719184853471951 / 58720256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 6 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((14868649882686113601405 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 6 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((15200735648633494574775 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 6 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-172161959433551259915 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 6 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-45588669081462457157175 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 6 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-110234822092806509505 / 33554432) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD6R3S5 :
    OAI.Laughlin.Certificate.errorRational 6 (1 : Fin 3) (2 : Fin 3) =
      TorusLean.FermionM3.errorTable06 (1 : Fin 3) (2 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 6 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD6R3S5Row0,
    originalYRowSplitD6R3S5Row1,
    originalYRowSplitD6R3S5Row2,
    originalYRowSplitD6R3S5Row3,
    originalYRowSplitD6R3S5Row4,
    originalYRowSplitD6R3S5Row5,
    originalYRowSplitD6R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable06]

#print axioms originalYEntrySplitD6R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
