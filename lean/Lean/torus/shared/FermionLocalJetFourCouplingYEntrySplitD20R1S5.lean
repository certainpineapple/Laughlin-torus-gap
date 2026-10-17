import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 20 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 20 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 20 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 20 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 20 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((5040940008672192266119603125 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 20 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((243151623398195497218358125 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 20 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-64130730817312652527618959375 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R1S5 :
    OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (2 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (0 : Fin 10) (2 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R1S5Row0,
    originalYRowSplitD20R1S5Row1,
    originalYRowSplitD20R1S5Row2,
    originalYRowSplitD20R1S5Row3,
    originalYRowSplitD20R1S5Row4,
    originalYRowSplitD20R1S5Row5,
    originalYRowSplitD20R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
