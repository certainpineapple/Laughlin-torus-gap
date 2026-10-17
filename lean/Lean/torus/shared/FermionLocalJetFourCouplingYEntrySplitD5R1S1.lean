import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD5R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 5 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((288217185514048371 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 5 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((117686364357605208465 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 5 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((45543850761592353716265 / 3758096384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 5 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((-33527805633645391850149 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 5 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((307361222967220883631 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 5 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((10589763940221275062345 / 536870912) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD5R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 5 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-192715136303794262991 / 33554432) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD5R1S1 :
    OAI.Laughlin.Certificate.errorRational 5 (0 : Fin 3) (0 : Fin 3) =
      TorusLean.FermionM3.errorTable05 (0 : Fin 3) (0 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 5 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD5R1S1Row0,
    originalYRowSplitD5R1S1Row1,
    originalYRowSplitD5R1S1Row2,
    originalYRowSplitD5R1S1Row3,
    originalYRowSplitD5R1S1Row4,
    originalYRowSplitD5R1S1Row5,
    originalYRowSplitD5R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable05]

#print axioms originalYEntrySplitD5R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
