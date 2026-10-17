import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD20R11S13Row0 :
    OAI.Laughlin.Certificate.yRow 20 11 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R11S13Row1 :
    OAI.Laughlin.Certificate.yRow 20 11 13
      (OAI.Laughlin.Certificate.rows[1]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R11S13Row2 :
    OAI.Laughlin.Certificate.yRow 20 11 13
      (OAI.Laughlin.Certificate.rows[2]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R11S13Row3 :
    OAI.Laughlin.Certificate.yRow 20 11 13
      (OAI.Laughlin.Certificate.rows[3]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R11S13Row4 :
    OAI.Laughlin.Certificate.yRow 20 11 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-698327332120036021528125 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R11S13Row5 :
    OAI.Laughlin.Certificate.yRow 20 11 13
      (OAI.Laughlin.Certificate.rows[5]!) = (-354424005932180129946000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD20R11S13Row6 :
    OAI.Laughlin.Certificate.yRow 20 11 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((662426981028083081435625 / 2) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD20R11S13 :
    OAI.Laughlin.Certificate.errorRational 20 (5 : Fin 10) (6 : Fin 10) =
      TorusLean.FermionM3.errorTable20 (5 : Fin 10) (6 : Fin 10) := by
  change OAI.Laughlin.Certificate.Y 20 11 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD20R11S13Row0,
    originalYRowSplitD20R11S13Row1,
    originalYRowSplitD20R11S13Row2,
    originalYRowSplitD20R11S13Row3,
    originalYRowSplitD20R11S13Row4,
    originalYRowSplitD20R11S13Row5,
    originalYRowSplitD20R11S13Row6]
  norm_num [TorusLean.FermionM3.errorTable20]

#print axioms originalYEntrySplitD20R11S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
