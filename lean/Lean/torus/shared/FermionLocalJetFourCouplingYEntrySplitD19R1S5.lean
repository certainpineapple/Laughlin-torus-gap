import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 19 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 19 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 19 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 19 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 19 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((296243074409419599675169831875 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 19 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1447870302842918504712790753125 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 19 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((62214676835648605625029798125 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R1S5 :
    OAI.Laughlin.Certificate.errorRational 19 (0 : Fin 10) (2 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (0 : Fin 10) (2 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R1S5Row0,
    originalYRowSplitD19R1S5Row1,
    originalYRowSplitD19R1S5Row2,
    originalYRowSplitD19R1S5Row3,
    originalYRowSplitD19R1S5Row4,
    originalYRowSplitD19R1S5Row5,
    originalYRowSplitD19R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
