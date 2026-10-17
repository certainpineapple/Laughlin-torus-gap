import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R1S7Row0 :
    OAI.Laughlin.Certificate.yRow 16 1 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((6410943036420535738125 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S7Row1 :
    OAI.Laughlin.Certificate.yRow 16 1 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((535396932285722056675125 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S7Row2 :
    OAI.Laughlin.Certificate.yRow 16 1 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-13729510657037413948334625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S7Row3 :
    OAI.Laughlin.Certificate.yRow 16 1 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((206312273689473722968572375 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S7Row4 :
    OAI.Laughlin.Certificate.yRow 16 1 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((285737800932836935579771875 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S7Row5 :
    OAI.Laughlin.Certificate.yRow 16 1 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2663557287492206477379632625 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S7Row6 :
    OAI.Laughlin.Certificate.yRow 16 1 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((34651180964092750972039125 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R1S7 :
    OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (3 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (0 : Fin 8) (3 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 1 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R1S7Row0,
    originalYRowSplitD16R1S7Row1,
    originalYRowSplitD16R1S7Row2,
    originalYRowSplitD16R1S7Row3,
    originalYRowSplitD16R1S7Row4,
    originalYRowSplitD16R1S7Row5,
    originalYRowSplitD16R1S7Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R1S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
