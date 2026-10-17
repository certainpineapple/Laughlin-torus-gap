import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R13S13Row0 :
    OAI.Laughlin.Certificate.yRow 20 13 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S13Row1 :
    OAI.Laughlin.Certificate.yRow 20 13 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S13Row2 :
    OAI.Laughlin.Certificate.yRow 20 13 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S13Row3 :
    OAI.Laughlin.Certificate.yRow 20 13 13
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S13Row4 :
    OAI.Laughlin.Certificate.yRow 20 13 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((145595360660101936959375 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S13Row5 :
    OAI.Laughlin.Certificate.yRow 20 13 13
      (OAI.Laughlin.Certificate.rows[5]!) = (1126933227098755210134000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R13S13Row6 :
    OAI.Laughlin.Certificate.yRow 20 13 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-2870516917788360019554375 / 8) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R13S13 :
    OAI.Laughlin.Certificate.errorRational 20 (6 : Fin 10) (6 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (6 : Fin 10) (6 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 13 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R13S13Row0,
    originalYRowSplitD20R13S13Row1,
    originalYRowSplitD20R13S13Row2,
    originalYRowSplitD20R13S13Row3,
    originalYRowSplitD20R13S13Row4,
    originalYRowSplitD20R13S13Row5,
    originalYRowSplitD20R13S13Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R13S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
