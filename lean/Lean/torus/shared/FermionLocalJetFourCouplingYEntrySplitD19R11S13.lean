import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD19R11S13Row0 :
    OAI.Laughlin.Certificate.yRow 19 11 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R11S13Row1 :
    OAI.Laughlin.Certificate.yRow 19 11 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R11S13Row2 :
    OAI.Laughlin.Certificate.yRow 19 11 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R11S13Row3 :
    OAI.Laughlin.Certificate.yRow 19 11 13
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R11S13Row4 :
    OAI.Laughlin.Certificate.yRow 19 11 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-30782578328254959983902125 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R11S13Row5 :
    OAI.Laughlin.Certificate.yRow 19 11 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((55885475686396247007991875 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD19R11S13Row6 :
    OAI.Laughlin.Certificate.yRow 19 11 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((848967450480031203696375 / 64) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD19R11S13 :
    OAI.Laughlin.Certificate.errorRational 19 (5 : Fin 10) (6 : Fin 10) =
      TorusLean.FermionM3.errorTable19 (5 : Fin 10) (6 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 19 11 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD19R11S13Row0,
    originalYRowSplitD19R11S13Row1,
    originalYRowSplitD19R11S13Row2,
    originalYRowSplitD19R11S13Row3,
    originalYRowSplitD19R11S13Row4,
    originalYRowSplitD19R11S13Row5,
    originalYRowSplitD19R11S13Row6]
  norm_num [TorusLean.FermionM3.errorTable19]

#print axioms originalYEntrySplitD19R11S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
