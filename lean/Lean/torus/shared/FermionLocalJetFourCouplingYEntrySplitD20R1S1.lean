import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 20 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 20 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 20 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 20 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 20 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((68252194813324049200807509375 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 20 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((4019361491023681820676033375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 20 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2590505281061257362145653184875 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R1S1 :
    OAI.Laughlin.Certificate.errorRational 20 (0 : Fin 10) (0 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (0 : Fin 10) (0 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R1S1Row0,
    originalYRowSplitD20R1S1Row1,
    originalYRowSplitD20R1S1Row2,
    originalYRowSplitD20R1S1Row3,
    originalYRowSplitD20R1S1Row4,
    originalYRowSplitD20R1S1Row5,
    originalYRowSplitD20R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
