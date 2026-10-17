import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 9 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((400089433880694285 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 9 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-23061855349751721471 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 9 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((11307906623103573624885 / 4194304) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 9 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-4161983511688686307935 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 9 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((18887953202641611924345 / 117440512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 9 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((72763118140234198124925 / 29360128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 9 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-33968895069261297015 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R3S5 :
    OAI.Laughlin.Certificate.errorRational 9 (1 : Fin 5) (2 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (1 : Fin 5) (2 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R3S5Row0,
    originalYRowSplitD9R3S5Row1,
    originalYRowSplitD9R3S5Row2,
    originalYRowSplitD9R3S5Row3,
    originalYRowSplitD9R3S5Row4,
    originalYRowSplitD9R3S5Row5,
    originalYRowSplitD9R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
